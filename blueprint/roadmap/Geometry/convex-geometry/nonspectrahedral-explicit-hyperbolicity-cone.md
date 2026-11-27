# An explicit hyperbolicity cone that is not spectrahedral

Work on $V=\operatorname{Sym}_4(\mathbb R)^2\times\mathbb R^3$ (dimension $23$) with base point $e=(I,I,0)$. For $y\in\mathbb R^3$, set $Q_{ii}=y_i^2+y_{i+1}^2$ (indices modulo $3$) and $Q_{ij}=-y_iy_j$ off the diagonal. For a symmetric block matrix $A=\begin{pmatrix}a&b^{\mathsf T}\\b&C\end{pmatrix}$ with scalar first block, put $\Phi_y(A)=\begin{pmatrix}\operatorname{tr}(QC)&-b^{\mathsf T}Q\\-Qb&aQ\end{pmatrix}$. Define $P(X,Z,y)=\det((\det X)Z-\Phi_y(\operatorname{adj}X))$ in independent upper-triangular coordinates. It is homogeneous of total degree $20$, has $P(e)=1$, and for every $x\in V$ all complex roots of $t\mapsto P(te-x)$ are real. The cone of $x$ for which these roots are all nonnegative is not the positive-semidefinite region of any linear map $V\to\operatorname{Sym}_N(\mathbb R)$ at any integer $N>0$. This excludes direct spectrahedral representations, not semidefinite lifts with auxiliary variables.

## Depends on
Real symmetric matrix coordinates, polynomial evaluation on the line with sign $te-x$, and the positive-semidefinite matrix cone.

## Proof depends on
A real-rootedness argument for the explicit determinant and a separate obstruction to all linear matrix pencils.

## Expansion
Check the cyclic diagonals of $Q$, the homogeneous-degree and base-point computations, and then separate the real-rootedness and nonspectrahedral obstruction. Do not replace the linear-pencil obstruction with the stronger projected Lax statement.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HyperbolicCones.lean#L67-L76) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/095.md).
