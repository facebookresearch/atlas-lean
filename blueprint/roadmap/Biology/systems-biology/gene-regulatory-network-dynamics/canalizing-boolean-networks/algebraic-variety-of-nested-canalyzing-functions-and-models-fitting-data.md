# Algebraic variety of nested canalyzing functions and nested canalyzing models fitting data

**Setting.** Boolean functions $h : \mathbb{F}_2^n \to \mathbb{F}_2$ are identified with square-free polynomials $h = \sum_{S \subseteq [n]} c_S\prod_{i\in S}x_i$ in $R = \mathbb{F}_2[x_1,\dots,x_n]/\langle x_i^2 - x_i\rangle$, i.e. with coefficient vectors $(c_S) \in \mathbb{F}_2^{2^n}$. $h$ is *nested canalyzing* (NCF) with respect to a permutation $\sigma$, canalyzing inputs $a_i$ and canalyzed outputs $b_i$ if $h = b_1$ when $x_{\sigma(1)} = a_1$; otherwise $h = b_2$ when $x_{\sigma(2)} = a_2$; ...; otherwise $h = b_n$ when $x_{\sigma(n)} = a_n$, and $h = \bar b_n$ if no variable takes its canalyzing value. For $S \ne \emptyset$ let $r_S^\sigma$ be the $\sigma$-largest element of $S$ and $[r_S^\sigma] = \{\sigma(1), \dots, r_S^\sigma\}$ its completion.

**Theorem (coefficient characterisation).** $h$ is nested canalyzing with respect to $\sigma$ (for some inputs and outputs) if and only if $c_{[n]} = 1$ and, for every proper subset $S \subseteq [n]$,

$$c_S = c_{[r_S^\sigma]}\prod_{\sigma(i) \in [r_S^\sigma]\setminus S} c_{[n]\setminus\{\sigma(i)\}}.$$

Hence the NCFs with respect to $\sigma$ form the variety $V_\sigma^{\mathrm{ncf}} \subset \mathbb{F}_2^{2^n}$ cut out by these binomial-type equations, and all NCFs form $V^{\mathrm{ncf}} = \bigcup_\sigma V_\sigma^{\mathrm{ncf}}$, with ideal $\mathbb{I}(V^{\mathrm{ncf}})$.

**Theorem (models fitting data).** Let $D = \{(\mathbf{s}_j, t_j)\}_{j=1}^r$ be input–output data for one network node, $f$ any interpolating polynomial and $I = \langle\prod_{j}(1 - \prod_e(1 - (x_e - s_{j,e})))\rangle$ the ideal of functions vanishing on the inputs, so the set of all models fitting $D$ is $f + I$. Writing $f + g\cdot p$ with $g = \sum_H b_H\prod_{i\in H}x_i$ and collecting coefficients $c_S = W_S(b_H, \mathbf{s}_j, t_j)$, the kernel of the ring map $\Phi : \bar{\mathbb{F}}_2[c_S] \to \bar{\mathbb{F}}_2[b_H]$, $c_S \mapsto W_S$, is the ideal of all polynomials fitting $D$, and the ideal of all nested canalyzing functions fitting $D$ is

$$\mathbb{I}(V^{\mathrm{ncf}}) + \ker\Phi.$$

Its $\mathbb{F}_2$-rational points (computable by Gröbner bases) are exactly the NCF models consistent with the data.

## Proof sketch

Writing an NCF as nested products $h = \bar b_n + \prod(x_{\sigma(1)} - a_1)\cdots$ and expanding shows that the top coefficient $c_{[n]} = 1$ and each lower coefficient factors through the coefficients $c_{[n]\setminus\{\sigma(i)\}}$, which encode the canalyzing input values, and the prefix coefficients $c_{[r_S^\sigma]}$, which encode the outputs; conversely such factorisations reassemble into the nested form. Intersecting the elimination-theoretic description of all data-consistent polynomials with the NCF variety restricts the huge model space $f + I$ to biologically motivated regulatory rules, since nested canalyzing rules are stable and common in gene regulatory networks.

## Sources

- Franziska Hinkelmann and Abdul Salam Jarrah, "Inferring Biologically Relevant Models: Nested Canalyzing Functions", *ISRN Biomathematics* 2012 (2012), 1–7, <https://doi.org/10.5402/2012/613174>. Preprint version: arXiv:1011.6064 (2010), Section 2 (definition, coefficient theorem and variety $V_\sigma^{\mathrm{ncf}}$) and Section 3 (ideal of nested canalyzing models fitting data), <https://doi.org/10.48550/arXiv.1011.6064>.
