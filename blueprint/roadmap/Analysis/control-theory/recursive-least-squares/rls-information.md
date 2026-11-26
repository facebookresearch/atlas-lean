# Information matrix of recursive least squares

The matrix $P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top$, where $P_0^{-1}$ is the inverse of $P_0$ when $P_0$ is
invertible and $0$ otherwise. For positive definite $P_0$ it is the inverse of the
RLS matrix $P_t$ ([the RLS matrix is the inverse of the information matrix](rls-snd-eq-inv.md)); its smallest
eigenvalue measures how much the data excite all directions of the parameter.
