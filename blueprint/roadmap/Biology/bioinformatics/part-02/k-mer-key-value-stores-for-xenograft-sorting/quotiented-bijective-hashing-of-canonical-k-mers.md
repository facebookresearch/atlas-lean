# Quotiented bijective hashing of canonical k-mers

Encode nucleotides as $A \mapsto 0$, $C \mapsto 1$, $G \mapsto 2$, $T \mapsto 3$, read a $k$-mer as a base-4 integer, and define its **canonical code** as the maximum of the codes of the $k$-mer and of its reverse complement. For odd $k$ no $k$-mer equals its reverse complement, so there are exactly $c(k) = 4^k/2$ canonical codes, all lying in $K = \{0, \dots, 4^k - 1\}$.

**Lemma (affine bijection).** For a $2k$-bit offset $b$ and an odd $2k$-bit multiplier $a$, the map

$$g_{a,b}(x) = \big[a \cdot (\mathrm{rot}_k(x) \oplus b)\big] \bmod 4^k,$$

where $\mathrm{rot}_k$ cyclically rotates the $2k$-bit word by $k$ bits and $\oplus$ is bitwise exclusive or, is a bijection of $K$, with inverse $x = \mathrm{rot}_k\big([(a' y) \bmod 4^k] \oplus b\big)$, where $a a' \equiv 1 \pmod{4^k}$.

**Quotienting.** With $p$ buckets and bucket function $f(x) = g(x) \bmod p$, the key is recoverable from its bucket index and the quotient $q(x) = \lfloor g(x)/p \rfloor$, since $g(x) = p\, q(x) + f(x)$ and $g$ is invertible. So a slot needs only $\lceil 2k - \log_2 p \rceil$ bits for the key, plus $\lceil \log_2(h+1) \rceil$ bits recording which of the $h$ hash functions placed it, plus the value bits.

**Hamming-1 neighbours.** For $k = 2\ell + 1$, two $k$-mers at Hamming distance $1$ differ in their $\ell$-suffix, in the $\ell$-suffix of their reverse complements, or in their middle base. Hence all **weak** $k$-mers (species-exclusive $k$-mers with a Hamming-1 neighbour in the other species) are found by sorting the $k$-mer list together with reverse complements, scanning blocks of equal $(\ell+1)$-prefix, and re-sorting blocks of equal $\ell$-prefix with middle base and suffix swapped.

## Expansion

Since $4^k$ is a power of two and $a$ is odd, $a$ is invertible modulo $4^k$ (extended Euclid), and rotation and xor are involutions; this proves the lemma. The rotation moves the low-entropy high bits created by the max in the canonical code into the interior before multiplication. In a $(3,4)$ bucketed Cuckoo table with $k = 25$ and about $1.28 \times 10^9$ buckets, each entry takes $2 + 3 + 20 = 25$ bits (hash choice, species value, quotient). Each read is then classified by counting host, graft, both and weak $k$-mers.

## Sources

- J. Zentgraf and S. Rahmann, "Fast lightweight accurate xenograft sorting", Algorithms for Molecular Biology 16 (2021), 2, Methods ("Key-value stores of canonical k-mers", "Bijective hash functions and quotienting", Lemma 1, "Annotating weak k-mers", Observation 1), <https://doi.org/10.1186/s13015-021-00181-w>, PMCID: PMC8017614.
