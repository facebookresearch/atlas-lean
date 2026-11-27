# Kalman subspace

Let $E$ and $U$ be real inner product spaces, let $A : E \to E$ and $B : U \to E$ be bounded linear maps, and let $n = \dim E$ when $E$ is finite-dimensional and $n = 0$ otherwise. The **Kalman subspace** of $(A, B)$ is

$$\operatorname{Span} \{ A^i B u : u \in U, \ 0 \le i < n \},$$

so it is $\{0\}$ when $E$ is infinite-dimensional. For finite-dimensional $E$ and $U$ it is the column space of the Kalman matrix $[B, AB, \dots, A^{n-1} B]$, and the **Kalman rank condition** says that it is all of $E$ (Coron, *Control and Nonlinearity*, AMS 2007, Theorem 1.16, condition (1.29); Sontag, *Mathematical Control Theory*, 2nd ed., the reachability matrix $R(A, B)$ of Theorem 3).

