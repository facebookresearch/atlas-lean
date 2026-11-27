# Ford's alpha-model of random binary trees

**Objects.** Trees are rooted binary trees; a *cladogram* on $[n]=\{1,\ldots,n\}$ is a tree with leaves bijectively labelled by $[n]$. Write $\mathcal{BT}^*_n$, $\mathcal{BT}_n$ for unlabelled trees (shapes) and cladograms with $n$ leaves, and $\mathcal{OBT}^*_n$, $\mathcal{OBT}_n$ for their ordered versions (children of each internal node ordered). For an internal node $v$ with children $v_1,v_2$, its *numerical split* is $NS_T(v)=(\kappa_T(v_1),\kappa_T(v_2))$, the numbers of descendant leaves (ordered as in the tree, or increasingly for unordered trees); $NS(T)$ is the multiset of numerical splits. A *symmetric branch point* is an internal node whose two child subtrees are isomorphic. $T\star T'$ denotes the root join of two trees.

**The model.** Fix $\alpha\in[0,1]$. Grow a cladogram from a single leaf labelled $1$; for $m=2,\ldots,n$ insert leaf $m$ either on an arc (subdividing it) or above the current root, choosing

- a given pendant arc with probability $\dfrac{1-\alpha}{m-1-\alpha}$,
- a given internal arc, or the new-root position, with probability $\dfrac{\alpha}{m-1-\alpha}$.

The probability $P^{(*)}_{\alpha,n}$ of a shape is the total probability of all growth histories producing it, and the probabilities $P_{\alpha,n}$ on cladograms, $P^{(o,*)}_{\alpha,n}$ on ordered shapes and $P^{(o)}_{\alpha,n}$ on ordered cladograms are obtained by spreading each shape's probability uniformly over its preimages. The values $\alpha=0$ and $\alpha=1/2$ recover the Yule (ERM) and uniform (PDA) models.

**Markov branching for ordered shapes.** Let $\Gamma_\alpha(1)=1$ and $\Gamma_\alpha(n)=(n-1-\alpha)\,\Gamma_\alpha(n-1)$ for $n\ge 2$, and for $a,b\ge 1$

$$\varphi_\alpha(a,b) = \frac{\alpha}{2}\binom{a+b}{a} + (1-2\alpha)\binom{a+b-2}{a-1}, \qquad q_\alpha(a,b) = \frac{\Gamma_\alpha(a)\,\Gamma_\alpha(b)}{\Gamma_\alpha(a+b)}\,\varphi_\alpha(a,b).$$

Then for $0<m<n$ and ordered shapes $T^*_m\in\mathcal{OBT}^*_m$, $T^*_{n-m}\in\mathcal{OBT}^*_{n-m}$,

$$P^{(o,*)}_{\alpha,n}(T^*_m\star T^*_{n-m}) = q_\alpha(m,n-m)\,P^{(o,*)}_{\alpha,m}(T^*_m)\,P^{(o,*)}_{\alpha,n-m}(T^*_{n-m}).$$

## Expansion

Each insertion step multiplies by a factor depending only on whether the chosen arc is pendant or internal, so the probability of a history factorises. Summing over histories that put a given set of $m$ labels in the left subtree of the root gives the split weight $q_\alpha(m,n-m)$, and the two subtrees then evolve as independent copies of the model, which is the Markov branching property for ordered shapes. The explicit closed forms for cladograms and unordered shapes are in probabilities of cladograms and tree shapes under Ford's model.

## Sources

- Tomás M. Coronado, Arnau Mir, Francesc Rosselló, "The Probabilities of Trees and Cladograms under Ford’s α-Model", The Scientific World Journal 2018 (2018), 1–7, <https://doi.org/10.1155/2018/1916094>. Published version of arXiv:1801.03843, cited next; locators there refer to the arXiv version.
- Tomás M. Coronado, Arnau Mir and Francesc Rosselló, "The probabilities of trees and cladograms under Ford's $\alpha$-model", arXiv:1801.03843 (2018), Section 2 (definitions, the $\alpha$-model and Proposition 1), Section 3 (Proposition 2, Corollaries 1 and 2 and the accompanying remarks), <https://doi.org/10.48550/arXiv.1801.03843>.
