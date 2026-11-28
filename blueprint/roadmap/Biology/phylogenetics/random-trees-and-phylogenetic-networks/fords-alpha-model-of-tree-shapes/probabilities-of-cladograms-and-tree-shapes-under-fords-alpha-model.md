# Probabilities of cladograms and tree shapes under Ford's alpha-model

**Setting.** Under Ford's $\alpha$-model ($\alpha\in[0,1]$) with $\Gamma_\alpha(1)=1$, $\Gamma_\alpha(n)=(n-1-\alpha)\Gamma_\alpha(n-1)$, and

$$\varphi_\alpha(a,b) = \frac{\alpha}{2}\binom{a+b}{a} + (1-2\alpha)\binom{a+b-2}{a-1},$$

let $NS(T)$ be the multiset of numerical splits $(\kappa(v_1),\kappa(v_2))$ over the internal nodes of a rooted binary tree $T$, with $q_\alpha(a,b)=\frac{\Gamma_\alpha(a)\Gamma_\alpha(b)}{\Gamma_\alpha(a+b)}\varphi_\alpha(a,b)$.

**Cladograms.** For every cladogram $T\in\mathcal{BT}_n$ on $[n]$,

$$P_{\alpha,n}(T) = \frac{2^{n-1}}{n!\,\Gamma_\alpha(n)}\prod_{(a,b)\in NS(T)}\varphi_\alpha(a,b).$$

Consequently, for $0<m<n$ and cladograms $T_m\in\mathcal{BT}_m$, $T_{n-m}\in\mathcal{BT}_{n-m}$ on complementary label sets,

$$P_{\alpha,n}(T_m\star T_{n-m}) = \frac{2\,q_\alpha(m,n-m)}{\binom{n}{m}}\,P_{\alpha,m}(T_m)\,P_{\alpha,n-m}(T_{n-m}).$$

**Tree shapes.** For an unlabelled shape $T^*\in\mathcal{BT}^*_n$ with $k$ symmetric branch points,

$$P^{(*)}_{\alpha,n}(T^*) = \frac{2^{n-k-1}}{\Gamma_\alpha(n)}\prod_{(a,b)\in NS(T^*)}\varphi_\alpha(a,b).$$

**Corrections to earlier statements.** (i) The previously published cladogram formula, which carries a factor $2^{k+m}$ with $k$ symmetric branch points and $m$ internal nodes with unequal split sizes, disagrees with the formula above whenever some internal node has two child subtrees with equal leaf counts but different shapes; the first such cladogram, and up to relabelling the only one with at most 8 leaves, is $((1,(2,(3,4))),((5,6),(7,8)))$. (ii) The shape probabilities $P^{(*)}_{\alpha,n}$ do *not* satisfy a Markov branching recurrence: for two distinct shapes $T_m,T'_m$ with the same $m$ and $k$, $P^{(*)}(T_m\star T_m)=q_\alpha(m,m)P^{(*)}(T_m)^2$ whereas $P^{(*)}(T_m\star T'_m)=2q_\alpha(m,m)P^{(*)}(T_m)P^{(*)}(T'_m)$, so no single split weight works (for example $T_m=(*,((*,*),(*,(*,*))))$ and $T'_m=((*,*),(*,(*,(*,*))))$ with $m=6$).

## Depends on

- [Ford's alpha-model of random binary trees](fords-alpha-model.md)

## Expansion

Start from the Markov branching recurrence for ordered shapes and unfold it to a product over internal nodes; the $\Gamma_\alpha$ factors telescope to $1/\Gamma_\alpha(n)$, leaving $\prod\varphi_\alpha$. An ordered cladogram is obtained from an ordered shape by one of $n!$ labellings, and each unordered cladogram has exactly $2^{n-1}$ orderings (labels break all symmetries), which gives the cladogram formula. For unlabelled shapes the number of orderings is $2^{n-1-k}$, since a symmetric branch point yields isomorphic ordered trees under swapping its children. The non-Markov phenomenon for shapes comes from exactly this dependence on symmetric branch points, which is not determined by the subtrees' probabilities alone.

## Sources

- Tomás M. Coronado, Arnau Mir, Francesc Rosselló, "The Probabilities of Trees and Cladograms under Ford’s α-Model", The Scientific World Journal 2018 (2018), 1–7, <https://doi.org/10.1155/2018/1916094>. Published version of arXiv:1801.03843, cited next; locators there refer to the arXiv version.
- Tomás M. Coronado, Arnau Mir and Francesc Rosselló, "The probabilities of trees and cladograms under Ford's $\alpha$-model", arXiv:1801.03843 (2018), Section 2 (definitions, the $\alpha$-model and Proposition 1), Section 3 (Proposition 2, Corollaries 1 and 2 and the accompanying remarks), <https://doi.org/10.48550/arXiv.1801.03843>.
