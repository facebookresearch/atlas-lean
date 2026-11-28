# Semialgebraic description of the three-leaf general Markov model

**Model.** On a star tree with one hidden internal node and three observed leaves, all variables have $n$ states. The hidden variable has distribution $\boldsymbol\pi$ with strictly positive entries, and leaf $i$ is obtained through an $n\times n$ non-singular stochastic matrix $M_i$ (non-negative entries, unit row sums). The joint leaf distribution is the tensor

$$P=\operatorname{Diag}(\boldsymbol\pi)(M_1,M_2,M_3), \qquad P_{abc}=\sum_{h=1}^n \pi_h\,M_1(h,a)\,M_2(h,b)\,M_3(h,c).$$

For $n=4$ this is the general Markov model of DNA substitution on a $3$-taxon tree; the same model is the latent class (hidden naive Bayes) model. Write $P*_i\mathbf 1$ for the two-leaf marginal obtained by summing over the $i$-th index, $\mathbf e_l$ for standard basis vectors and $f_i$ for the [Hessian-determinant invariants](hessian-determinant-invariants-of-rank-n-tensors.md).

**Proposition (Section 7).** An $n\times n\times n$ tensor $P$ lies in the image of the parametrization if and only if:

1. $P$ is real with non-negative entries summing to $1$;
2. for some (hence every) $i$, $P$ satisfies the commutation relations and $f_i(P;\mathbf x)\not\equiv 0$;
3. $\det(P*_i\mathbf 1)\neq 0$ for $i=1,2,3$;
4. for at least one (hence all) of the matrices

$$\det(P*_1\mathbf 1)\,(P*_2\mathbf 1)\operatorname{adj}(P*_1\mathbf 1)(P*_3\mathbf 1)^{T},\quad \det(P*_2\mathbf 1)\,(P*_1\mathbf 1)\operatorname{adj}(P*_2\mathbf 1)(P*_3\mathbf 1),\quad \det(P*_3\mathbf 1)\,(P*_1\mathbf 1)^{T}\operatorname{adj}(P*_3\mathbf 1)(P*_2\mathbf 1),$$

all leading principal minors are strictly positive;
5. for every $1\le l\le n$, all principal minors of

$$\det(P*_1\mathbf 1)(P*_2\mathbf 1)\operatorname{adj}(P*_1\mathbf 1)(P*_3\mathbf e_l)^{T},\quad \det(P*_1\mathbf 1)(P*_2\mathbf e_l)\operatorname{adj}(P*_1\mathbf 1)(P*_3\mathbf 1)^{T},\quad \det(P*_2\mathbf 1)(P*_1\mathbf e_l)\operatorname{adj}(P*_2\mathbf 1)(P*_3\mathbf 1)$$

are non-negative.

If the $M_i$ are required to have strictly positive entries, condition 5 becomes: all leading principal minors are strictly positive. The only equalities used are the normalization and the commutation relations; a full generating set of the ideal of the model is not needed.

## Expansion

Marginals factor as $P*_i\mathbf 1=M_j^T\operatorname{diag}(\boldsymbol\pi)M_k$, so condition 3 holds. After dividing by a positive determinant squared, the matrices in condition 4 equal $M_i^T\operatorname{diag}(\boldsymbol\pi)M_i$, which are positive definite, and Sylvester's criterion gives the minor conditions; the matrices in condition 5 equal $M_i^T\operatorname{diag}(\pi_h M_j(h,l))_hM_i$, which are positive semidefinite. Conversely, conditions 1–2 and the [orbit characterization](hessian-determinant-invariants-of-rank-n-tensors.md) write $P=D(g_1,g_2,g_3)$ with complex $g_i$ whose non-real rows come in conjugate pairs. Rescaling rows to unit sums gives $P=\operatorname{Diag}(\boldsymbol\pi)(M_1,M_2,M_3)$ with possibly complex entries. A conjugate pair of rows would make $M_i^T\operatorname{diag}(\boldsymbol\pi)M_i$ indefinite, contradicting condition 4, so all parameters are real and $\boldsymbol\pi>0$; condition 5 then forces each column of each $M_i$ to be non-negative.

## Depends on

- [Hessian-determinant invariants of rank-$n$ tensors](hessian-determinant-invariants-of-rank-n-tensors.md)

## Sources

- Elizabeth S. Allman, Peter D. Jarvis, John A. Rhodes and Jeremy G. Sumner, "Tensor rank, invariants, inequalities, and applications", arXiv:1211.3461 (2012), Section 7 (the proposition characterizing the image of the parametrization of the 3-leaf model, and its proof via Sylvester's criterion), <https://doi.org/10.48550/arXiv.1211.3461>. Published version: SIAM Journal on Matrix Analysis and Applications 34(3) (2013), 1014–1045, <https://doi.org/10.1137/120899066>; locators above refer to the arXiv version.
