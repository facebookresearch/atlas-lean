# Andrews' generalization of MacMahon's partition theorem

For all natural numbers $r$ and
$n$, the number of partitions of $n$ in which every part occurring an odd number of times occurs
at least $2r + 1$ times equals the number of partitions of $n$ in which every odd part is
congruent to $2r + 1$ modulo $4r + 2$.

For $r = 1$ this is MacMahon's partition theorem: the first condition says that no part occurs
exactly once, and the second that every part is even or congruent to $3$ modulo $6$.

The proof compares generating functions in $q$. Both sides factor through the product over the
even parts, and the remaining factors agree by Euler's theorem that partitions into odd parts and
partitions into distinct parts are equinumerous, applied with $q$ replaced by $q^{2r+1}$.

## Sources

- Beaullah Mugwangwavari and Darlison Nyirenda, "A Note on the Andrews-Ericksson-Petrov-Romick Bijection for MacMahon's Partition Theorem", Journal of Integer Sequences 24 (2021), Article 21.5.6, Theorem `andthm` (Andrews' generalization), source lines 113–115, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Nyirenda/nyir26.tex>. The paper attributes the result to Andrews.
