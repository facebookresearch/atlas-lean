# Circulatory residual as a modal force balance

For a load parameter $q \in \mathbb{R}$, a trajectory $z : \mathbb{R} \to \mathbb{R}^2$ and a time $t$, let

$$R(t) = z''(t) + 2\,z'(t) + z(t) - q\,J z(t)$$

be the residual of the normalized circulatory model, where $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ and $z'$, $z''$ denote the derivatives of $z$ and $z'$. The derivatives follow the convention that the derivative of a function at a point where it is not differentiable is $0$. Then

$$R(t) = M z''(t) + D z'(t) + K z(t) - q\,J z(t)$$

with mass matrix $M = I$, damping matrix $D = 2I$ and modal stiffness $K = \operatorname{diag}(1,1)$; that is, the model is the force balance of two unit modes driven by the circulatory generalized force $q\,J z$. The identity holds for every $q$, $z$ and $t$.
