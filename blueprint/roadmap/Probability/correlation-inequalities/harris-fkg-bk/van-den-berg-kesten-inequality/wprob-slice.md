# Weighted probability by conditioning on the first coordinate

Let $n \in \mathbb{N}$, $\varphi : \{0,\dots,n\} \times \{0,1\} \to \mathbb{R}$ and $S \subseteq \{0,1\}^{\{0,\dots,n\}}$. With $\psi_j = \varphi_{j+1}$ the weights of the remaining coordinates,

$$P_\varphi(S) = \varphi_0(0)\, P_\psi(S_0) + \varphi_0(1)\, P_\psi(S_1),$$

where $P$ is the [weighted probability](wprob.md) and $S_0, S_1$ are the [slices](slice.md) of $S$ at the first coordinate.
