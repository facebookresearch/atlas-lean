# Baby-step giant-step evaluation of a one-dimensional linear map in HElib

In HElib's plaintext ring, a one-dimensional linear map $w=\sum_{i<D}\kappa(i)\rho^i(v)$ in a good hypercube dimension of size $D$ equals $\sum_{k<h}\rho^{gk}\big(\sum_{j<g}\rho^{-gk}(\kappa(j+gk))\,\rho^j(v)\big)$ with $g=\lceil\sqrt D\,\rceil$ and $h=\lceil D/g\rceil$, so an encrypted $v$ needs only the rotations $\rho^j$ ($0<j<g$) and $\rho^{gk}$ ($0<k<h$).

*Setting* (Halevi and Shoup, §§2.2–2.3). Let $m\ge2$, let $p$ be a prime not dividing $m$, $r\ge1$, and $R_{p^r}=\mathbb{Z}[X]/(p^r,\Phi_m(X))$. For $t\in\mathbb{Z}_m^*$, $\theta_t:a(X)\mapsto a(X^t)$ is a ring automorphism of $R_{p^r}$. If $\Phi_m\equiv F_1\cdots F_\ell\pmod{p^r}$ with every $F_i$ of degree $d$, the order of $p$ modulo $m$, the Chinese remainder theorem gives $R_{p^r}\cong E^\ell$ with slot ring $E=\mathbb{Z}[X]/(p^r,F_1(X))$. A hypercube basis $g_1,\dots,g_n\in\mathbb{Z}_m^*$, with $D_s$ the order of $g_s$ in $\mathbb{Z}_m^*/\langle p,g_1,\dots,g_{s-1}\rangle$, indexes the slots by tuples $(e_1,\dots,e_n)$ with $0\le e_s<D_s$, and $\rho_s$ maps the slot $(\dots,e_s,\dots)$ to $(\dots,e_s+1\bmod D_s,\dots)$, rotating every hypercolumn in dimension $s$ by one. Every $\rho_s$ permutes the slots of $E^\ell$, so it is a ring automorphism of $R_{p^r}$. Dimension $s$ is *good* if the order of $g_s$ in $\mathbb{Z}_m^*$ is $D_s$; then $\rho_s^i=\theta_{g_s^i}$ (their Eq. (1)), so $\rho_s$ is realized by the single substitution $\theta_{g_s}$. A one-dimensional $E$-linear transformation in dimension $s$ has the form $v\mapsto\sum_{i<D_s}\kappa(i)\rho_s^i(v)$ with constants $\kappa(i)\in R_{p^r}$ (their Eq. (5)).

**Theorem** (§6.3). Let $s$ be a good dimension, $D=D_s$, $\rho=\rho_s$, $g=\lceil\sqrt D\,\rceil$, $h=\lceil D/g\rceil$, let $\kappa(0),\dots,\kappa(D-1)\in R_{p^r}$, and put $\kappa(i)=0$ for $D\le i<gh$. Then for every $v\in R_{p^r}$

$$
\sum_{i<D}\kappa(i)\rho^i(v)=\sum_{k<h}\rho^{gk}\Big(\sum_{j<g}\kappa'(j+gk)\,\rho^j(v)\Big),\qquad\kappa'(j+gk)=\rho^{-gk}\big(\kappa(j+gk)\big).
$$

The source's Algorithm 1 evaluates the right-hand side on a ciphertext, with $\theta=\theta_{g_s}$: compute $v_j=\theta^j(v)$ for $j<g$, then $w_k=\sum_{j<g}\kappa'(j+gk)v_j$ for $k<h$, then $w=\sum_{k<h}\theta^{gk}(w_k)$. It applies the automorphisms $\theta^j$ for $0<j<g$ and $\theta^{gk}$ for $0<k<h$, given key-switching matrices for them; §4.1 describes this as reducing the number of automorphisms from $O(D)$ to $O(\sqrt D)$. In a bad dimension (the order of $g_s$ in $\mathbb{Z}_m^*$ exceeds $D_s$; for example $m=5$, $p=19$, $g_s=2$ gives $D_s=2$ but order $4$) $\rho_s$ is still a ring automorphism of $R_{p^r}$, but it is not a single substitution $\theta_t$: by their Eqs. (2)–(3) its powers combine $\theta_{g_s^i}$ and $\theta_{g_s^{i-D}}$ with a 0–1 mask, and the source uses a revised Algorithm 2 (§6.4).

## Depends on

None.

## Proof depends on

None.

## Expansion

Split the index as $i=j+gk$ with $j<g$ and $k<h$, which covers $[0,gh)\supseteq[0,D)$, and factor $\rho^{gk}$ out of each group: $\kappa(j+gk)\rho^{j+gk}(v)=\rho^{gk}\big(\kappa'(j+gk)\rho^j(v)\big)$ because $\rho$ is a ring automorphism (in a good dimension, $\rho=\theta_{g_s}$); the padded terms with $D\le j+gk<gh$ are zero. The [diagonal method](diagonal-matrix-vector-product.md) is the corresponding decomposition for a full cyclic rotation of all slots.

## Sources

- Shai Halevi, Victor Shoup, "Faster Homomorphic Linear Transformations in HElib", CRYPTO 2018, LNCS 10991, DOI 10.1007/978-3-319-96884-1_4; section, equation and printed page numbers from the [authors' copy](https://shoup.net/papers/matmul.pdf): §§2.2–2.3 (pp. 4–5, Equations (1)–(3)), §3.1 (p. 7, Equation (5)), §4.1 (p. 8), §6.1 (p. 11) and §6.3 with Algorithm 1 (pp. 12–13) and §6.4 (p. 13).
