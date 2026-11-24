# Instability of the Nicholson–Bailey equilibrium

The Nicholson–Bailey host–parasitoid map is $f(H, P) = (\lambda H e^{-aP},\ cH(1 - e^{-aP}))$ on the closed quadrant, with $a, c > 0$ and $\lambda > 0$. For $\lambda > 1$ it has exactly one positive fixed point, $x^* = (\lambda\ln\lambda/((\lambda - 1) a c),\ \ln\lambda/a)$, and this fixed point is unstable (Nicholson–Bailey model article). The linearization makes this explicit. (C1) A positive fixed point requires $\lambda e^{-aP} = 1$, so $P = \ln\lambda/a$, which is positive if and only if $\lambda > 1$, and then $H = P/(c(1 - 1/\lambda))$ gives $x^*$. (C2) The Jacobian at $x^*$ is $\begin{pmatrix} 1 & -aH^* \\ c(1 - 1/\lambda) & caH^*/\lambda \end{pmatrix}$, with trace $1 + u$ and determinant $\lambda u$, where $u = \ln\lambda/(\lambda - 1) \in (0, 1)$. (C3) Since $\lambda\ln\lambda > \lambda - 1$ for $\lambda > 1$, $\lambda u > 1$, and since $(1 + u)^2 < 4 < 4\lambda u$, the eigenvalues are non-real with modulus $\sqrt{\lambda u} = \sqrt{\lambda\ln\lambda/(\lambda - 1)} > 1$. Lyapunov instability of $x^*$ for the nonlinear map follows from (C3) by the instability theorem for fixed points of $C^1$ maps whose linearization has an eigenvalue of modulus greater than $1$.

## Expansion

1. (C1) Existence and uniqueness of the positive fixed point, and its absence for $0 < \lambda \le 1$.
2. (C2) The Jacobian at $x^*$, its trace and determinant.
3. (C3) The non-real eigenvalues and their modulus, from $\lambda\ln\lambda > \lambda - 1$ for $\lambda > 1$.
4. The instability theorem for $C^1$ maps with an expanding eigenvalue, and its application to $f$.
5. Global behaviour of positive orbits (Jamieson and Reis 2018, as cited in the model article), as a separate statement.

## Sources

- Nicholson–Bailey model, Wikipedia. <https://en.wikipedia.org/wiki/Nicholson%E2%80%93Bailey_model>
- Original result: A. J. Nicholson and V. A. Bailey, The balance of animal populations. Part I, Proc. Zool. Soc. London 105 (1935), 551–598. <https://doi.org/10.1111/j.1096-3642.1935.tb01680.x> The model and the instability of its positive fixed point follow the Nicholson–Bailey model article.
