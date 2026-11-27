# Counting weakly self-dual codes

Let $n$ be even and call a binary linear code $C \subseteq \mathbb{F}_2^n$ *weakly self-dual* if
$\langle 1_n \rangle \subseteq C \subseteq C^{\perp}$, where $1_n$ is the all-ones word and $C^{\perp}$ the
[dual code](../../../InformationTheory/error-correcting-codes/linear-codes/dual.md). For $1 \le s \le k$, the number
$\sigma_{n,k,s}$ of $k$-dimensional weakly self-dual codes that contain a given $s$-dimensional weakly self-dual code depends
only on $n$, $k$ and $s$, not on the code chosen. Consequently, for an even-weight vector $v \notin \langle 1_n \rangle$, the
number of $k$-dimensional weakly self-dual codes $C$ with $v \in C^{\perp}$ does not depend on $v$; call this number $W$.
Hence, for $n \ge 4$ and $1 \le k \le n/2$, if

$$\big|\{ v \in \mathbb{F}_2^n : \mathrm{wt}(v) \text{ even},\ 1 \le \mathrm{wt}(v) < d \}\big| < \frac{2^{n-1} - 2}{2^{n-k} - 2}$$

and $d \le n$, some $k$-dimensional weakly self-dual code $C$ has $C^{\perp}$ of minimum distance at least $d$. Indeed every
$C^{\perp}$ lies in the even-weight subspace and contains $1_n$, so counting pairs ($C$, a vector of $C^{\perp}$ other than $0$
and $1_n$) gives $(2^{n-1} - 2) W = (2^{n-k} - 2) |\varphi|$ for the family $\varphi$ of these codes (nonempty: for instance
the subspaces of the span of the words $e_{2i-1} + e_{2i}$ that contain $1_n$); the even words of weight between $1$ and
$d - 1$, none equal to $1_n$, lie in fewer than $|\varphi|$ of the $C^{\perp}$. This is the greedy argument of the
[Gilbert–Varshamov lemma](greedy-gilbert-varshamov-lemma-for-code-families.md) carried out on the even-weight subspace, as
Calderbank and Shor apply it.

## Expansion

A sound expansion states and checks the counting argument of MacWilliams, Sloane and Thompson (*Good self dual codes
exist*, Discrete Math. 3 (1972), 153–162, Theorem 2.1 and its proof), which Calderbank and Shor cite in the strengthened
form stated here, and Calderbank and Shor's reduction of the count of codes with $v \in C^{\perp}$ to $\sigma_{n,k,2}$ and
$\sigma_{n,k+1,2}$ (Section V).

## Depends on

- [Dual code](../../../InformationTheory/error-correcting-codes/linear-codes/dual.md)

## Related topics

- [The greedy Gilbert–Varshamov lemma for code families](greedy-gilbert-varshamov-lemma-for-code-families.md): applies this uniformity to the codes $C^{\perp}$

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section V, equations (27)–(28), the statement on $\sigma_{n,k,s}$, the count that follows, and "This is all that is needed to apply the greedy argument used to establish the Gilbert–Varshamov bound".
