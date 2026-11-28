# Mod p counting principles need linear polynomial calculus degree in characteristic $q$ coprime to $p$

Over a field of characteristic $q$ with $q \nmid p$, and over the ring $\mathbb{Z}_q$ when $p$ and $q$ are relatively prime, every polynomial calculus refutation of the mod $p$ counting principle needs degree linear in $n$, while over $\mathbb{Z}_p$ (the field $\mathbb{F}_p$ when $p$ is prime) constant degree suffices: a linear degree gap between characteristics.

**Polynomial calculus.** Over a field $F$, a PC derivation from a set $Q$ of polynomials is a sequence $P_1, \dots, P_l$ in which each $P_i$ is in $Q$, or is $cP_j + dP_k$ for earlier $P_j, P_k$ and $c, d \in F$, or is $xP_j$ for an earlier $P_j$ and a variable $x$. A refutation derives $1$. Over a ring $R$ the rules are the same and a refutation derives a nonzero constant $r \in R$. The degree of a derivation is the maximum degree of its lines.

**Mod $p$ counting principle.** For $p \ge 2$, $\mathrm{MOD}^n_p$ has a variable $x_e$ for every $p$-element subset $e \subseteq [n]$ and the degree-$2$ equations

$$
x_e^2 - x_e = 0, \qquad x_e x_f = 0 \ (e \cap f \neq \emptyset,\ e \neq f), \qquad 1 - \sum_{e \ni i} x_e = 0 \ (i \in [n]),
$$

stating that $[n]$ is partitioned into blocks of size $p$; they have no $0/1$ solution when $p \nmid n$.

**Theorem.**

1. Let $q \ge 2$ be a prime with $q \nmid p$ and let $F$ be a field of characteristic $q$. Any PC refutation of the $\mathrm{MOD}^n_p$ polynomials over $F$ requires degree $> \delta n$, for some constant $\delta > 0$.
2. Let $p, q \ge 2$ be relatively prime. Any PC refutation over $\mathbb{Z}_q$ of the $\mathrm{MOD}^n_p$ polynomials requires degree $> \delta n$, for some constant $\delta > 0$ depending on $p$ and $q$.

## Expansion

The proof goes through a multiplicative mod $p$ Tseitin system $\mathrm{TS}_n(p)$ on an $r$-regular graph with expansion $\epsilon$, all charges $1$ and $n \equiv 1 \pmod p$: one variable $y_e$ per directed edge with $y_e^p - 1 = 0$, $y_{\langle i,j\rangle} y_{\langle j,i\rangle} - 1 = 0$, and $\prod_{j} y_{\langle i,j\rangle} - \omega = 0$ at each vertex, for a primitive $p$-th root of unity $\omega$ in $F$ (or in a finite ring $R \supset \mathbb{Z}_q$ in which $\omega^k - \omega^j$ is invertible for $0 \le j < k < p$, Theorem 23). All its equations are binomials, and a normal form for PC derivations from binomials (Theorem 6) shows that no refutation of $\mathrm{TS}_n(p)$ has degree $d < \epsilon n / 8$ over the field (Theorem 15), or $d < \epsilon n / 4$ over $R$ (Theorem 26). A low-degree reduction (Lemma 4) defines the Tseitin variables by degree-$2pr$ polynomials in the $\mathrm{MOD}^m_p$ variables, $m = n + nrp$, and derives the Tseitin equations in degree $2pr$; by Lemma 1 a degree-$d_3$ refutation of $\mathrm{MOD}^m_p$ yields one of $\mathrm{TS}_n(p)$ of degree $2pr \cdot d_3$, which forces $d_3 = \Omega(m)$ for constant $p, r, \epsilon$. Over $\mathbb{Z}_p$ (the field $\mathbb{F}_p$ when $p$ is prime, and over $\mathbb{Z}_{p_1 p_2}$ for $\mathrm{MOD}^n_{p_1}$ and $\mathrm{MOD}^n_{p_2}$) the counting principles have constant-degree refutations, so the bound separates characteristics linearly, the first gap larger than $\log \log n$. The paper's degree lower bounds for Tseitin tautologies (Theorem 10 for mod $2$, Corollary 21 for their Boolean mod $p$ versions $\mathrm{BTS}_{n,p}$) and the resulting worst-case exponential running time of Gröbner basis algorithms on 3-CNF formulas (Corollary 22) are not the subject of this page.

## Depends on

- [Cook-Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Dima Grigoriev, Russell Impagliazzo, Toniann Pitassi, "Linear Gaps between Degrees for the Polynomial Calculus Modulo Distinct Primes", *Journal of Computer and System Sciences*, 2001, doi:10.1006/jcss.2000.1726 (Corollary 20 and Corollary 27; Section 3 for $\mathrm{MOD}^n_p$, Lemmas 1 and 4; Theorems 6, 15, 23 and 26).
