# Kernels lemma

Let $R$ be a commutative ring, $M$ an $R$-module, $f$ an $R$-linear
endomorphism of $M$, and $(p_i)_{i \in \iota}$ a family of polynomials in $R[X]$, indexed by a
finite type $\iota$, that are pairwise coprime, meaning that for all $i \ne j$ there are
$a, b \in R[X]$ with $a p_i + b p_j = 1$. Then the submodules $\ker p_i(f)$ are independent
(each meets the sum of the others only in $0$), and their sum is
$\ker \bigl(\prod_{i \in \iota} p_i\bigr)(f)$.

The decomposition is internal to $\ker \bigl(\prod_{i \in \iota} p_i\bigr)(f)$; it need not span
all of $M$.

Proof: induction on the number of polynomials from the two-polynomial case, as in the cited French
Wikipedia article. For coprime $p$ and $q$ one has $\ker p(f) + \ker q(f) = \ker (pq)(f)$, which
gives the inductive step, and independence follows because $\ker p_i(f) \cap \ker q(f) = 0$ when
$q$ is the product of the other polynomials.

## Sources

- https://fr.wikipedia.org/wiki/Lemme_des_noyaux; S. Axler, Linear Algebra Done Right, 4th ed., Springer (2024), Section 8C.
