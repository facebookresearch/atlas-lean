# Sum-of-squares proofs need not have small coefficients

There are systems of polynomial equalities and inequalities over $\mathbb{R}^n$, with constant-degree constraints and integer coefficients of polynomial bit length, and a polynomial with a degree-$2$ sum-of-squares certificate of nonnegativity on their solutions, such that every degree-$2$ certificate has coefficients of bit complexity $2^{\Omega(n)}$, although degree-$4$ certificates of polynomial bit complexity exist (O'Donnell). Raghavendra and Weitz give a system of quadratic equations that includes the Boolean axioms $x_i^2 = x_i$ and a polynomial with a degree-$2$ certificate such that no certificate of degree $d \le \sqrt{n}$ has all coefficients smaller than $\Omega\big(n^{-d}\, 2^{\exp(\sqrt{n})}\big)$, so every such certificate needs $2^{\Omega(\sqrt{n})}$ bits.

Conversely (Raghavendra–Weitz), let $P = \{p_1, \dots, p_m\}$ and $Q = \{q_1, \dots, q_\ell\}$ be the equality and inequality constraints, let $S$ be a set of common zeros of $P$, and let $r$ be a polynomial nonnegative on $S$. Assume that the solutions are explicitly bounded, $\|\alpha\|_\infty \le 2^{\operatorname{poly}(n^d)}$ for all $\alpha \in S$, that the coefficients of $P$ and of $r$ are at most $2^{\operatorname{poly}(n^d)}$ in absolute value, and that $S$ is $(\delta, k, \epsilon)$-rich for $(P, Q)$ up to degree $d$:

- **spectral richness**: every nonzero eigenvalue of the degree-$d$ moment matrix $\mathbb{E}_{\alpha \in S}[v_d(\alpha) v_d(\alpha)^{\mathsf T}]$ of the uniform distribution on $S$ is at least $\delta$;
- **completeness**: every degree-$d$ polynomial in the kernel of that moment matrix has a degree-$k$ derivation from $P$;
- **robustness**: $q(\alpha) > \epsilon$ for every $q \in Q$ and $\alpha \in S$.

If $r$ has a degree-$d$ sum-of-squares certificate of nonnegativity from $P$ and $Q$, then it has a degree-$k$ certificate all of whose coefficients are bounded by $2^{\operatorname{poly}(n^k, \log(1/\delta), \log(1/\epsilon))}$. In particular, when $1/\delta, 1/\epsilon \le 2^{\operatorname{poly}(n^d)}$ and $k = O(d)$, every coefficient can be written with $\operatorname{poly}(n^d)$ bits. The theorem bounds the size of certificates only; it does not by itself provide an exact algorithm that finds one.

## Proof sketch

The counterexamples force, through a chain of quadratic constraints $y_{i+1} = y_i^2$, any low-degree certificate to contain doubly exponentially large multipliers; the Boolean version replaces each $y_i$ by a sum of Boolean variables. For the positive result, write the certificate as $r = \langle C, v v^{\mathsf T} \rangle + \sum_i \langle D_i, v v^{\mathsf T} \rangle q_i + \sum_i \lambda_i p_i$ with Gram matrices $C, D_i \succeq 0$. Completeness lets one move the components of $C$ and $D_i$ in the kernel of the moment matrix into the ideal part at degree $k$; averaging the identity over $S$, robustness and spectral richness bound the traces, hence the entries, of the remaining Gram matrices by $\operatorname{poly}(\|r\|, \|S\|, 1/\delta, 1/\epsilon)$. The new multipliers $\lambda_i'$ then solve a feasible linear system with bounded data, and Cramer's rule bounds their coefficients.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Sources

- R. O'Donnell, "SOS is not obviously automatizable, even approximately", ITCS (2017).
- P. Raghavendra, B. Weitz, "On the bit complexity of sum-of-squares proofs", ICALP (2017), LIPIcs 80, Art. 80, doi:10.4230/LIPIcs.ICALP.2017.80, arXiv:1702.05139 (Definition 5, Theorems 2 and 10).
