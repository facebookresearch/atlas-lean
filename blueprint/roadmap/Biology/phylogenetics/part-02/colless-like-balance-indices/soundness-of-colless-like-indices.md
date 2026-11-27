# Soundness of Colless-like indices

**Definitions.** Let $\mathcal T^*$ be the set of (unlabeled) rooted trees without out-degree-1 nodes, possibly multifurcating, and $f : \mathbb N \to \mathbb R_{\ge 0}$. The *$f$-size* of $T \in \mathcal T^*$ is

$$\delta_f(T) = \sum_{v \in V(T)} f(\deg(v)),$$

where $\deg(v)$ is the out-degree; it satisfies $\delta_f(T_1 \star \cdots \star T_k) = \delta_f(T_1) + \cdots + \delta_f(T_k) + f(k)$ for the tree whose root has subtrees $T_1, \dots, T_k$. (Taking $f(0) = 1$ and $f(n) = 0$ otherwise gives the number of leaves; $f \equiv 1$ gives the number of nodes.) Let $D$ be a dissimilarity on finite lists of non-negative reals, such as the mean deviation from the median (MDM), the sample standard deviation (sd) or the sample variance (var). For an internal node $v$ with children $v_1, \dots, v_k$, its *balance value* is $\mathrm{bal}_{D,f}(v) = D\bigl(\delta_f(T_{v_1}), \dots, \delta_f(T_{v_k})\bigr)$, and the *Colless-like index* is

$$C_{D,f}(T) = \sum_{v \in V_{int}(T)} \mathrm{bal}_{D,f}(v).$$

A tree is *fully symmetric* if at every internal node all child subtrees have the same shape. $C_{D,f}$ is *sound* if $C_{D,f}(T) = 0 \iff T$ is fully symmetric.

**Results.**

1. $C_{D,f}$ is sound if and only if $\delta_f(T_1) \ne \delta_f(T_2)$ for every pair of non-isomorphic fully symmetric trees $T_1, T_2$.
2. For $f(n) = e^n$ and for $f(n) = \ln(n + e)$, $C_{D,f}$ is sound for every dissimilarity $D$.
3. On bifurcating trees these indices reduce to the classical Colless index $C(T) = \sum_v |\kappa(v_1) - \kappa(v_2)|$ (with $\kappa$ the number of descendant leaves): $C_{\mathrm{MDM},f} = \frac{f(0)+f(2)}{2}\, C$, $C_{\mathrm{sd},f} = \frac{f(0)+f(2)}{\sqrt 2}\, C$ and $C_{\mathrm{var},f} = \frac{(f(0)+f(2))^2}{2}\, C^{(2)}$, where $C^{(2)}$ sums squared differences.
4. If $D$ costs $O(k)$ on $k$ values and each $f(k)$ costs $O(k)$, then $C_{D,f}(T)$ is computable in $O(n)$ time for $T$ with $n$ leaves.

## Proof depends on

- [Hermite–Lindemann theorem](../../../../NumberTheory/diophantine-approximation/transcendence-irrationality/hermite-lindemann.md)

## Expansion

If two different fully symmetric trees had equal $f$-size, joining them under a common root gives a non-symmetric tree with balance value $0$ at the root and $0$ elsewhere; conversely, if all fully symmetric trees have distinct $f$-sizes, induction from the leaves shows that a zero index forces equal child shapes at each node. Naive choices fail: with the leaf count as size, a node whose children are the star with four leaves and $FS_{2,2}$ can have zero dissimilarity. For $e^n$ and $\ln(n+e)$ the $f$-size of a fully symmetric tree $FS_{n_1,\dots,n_k}$ (root degree $n_1$, then $n_2$, ...) determines the sequence $(n_1, \dots, n_k)$, because $e$ is transcendental (Hermite–Lindemann): for $f(n) = e^n$ the $f$-size is $P(e)$ for a polynomial $P$ with non-negative integer coefficients that determines the sequence, and for $f(n) = \ln(n+e)$ it is $\ln Q(e)$ for a product $Q$ of linear factors $x + n$ that determines the sequence by unique factorization in $\mathbb Z[x]$; distinct polynomials take distinct values at a transcendental number.

## Sources

- A. Mir, L. Rotger and F. Rosselló, "Sound Colless-like balance indices for multifurcating trees", *PLoS ONE* 13(9) (2018) e0203401, Methods, Definition 4, Propositions 6–8, Definition 9, Lemma 10 and Propositions 16–17. <https://doi.org/10.1371/journal.pone.0203401> (PMC6155497)
