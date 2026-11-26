# Covariance of a correlated two-factor model

Let the two factors have unit variances and correlation $\varphi$. In the loading matrix $\Lambda$, indicators 1–3 load only on factor 1 and indicators 4–5 only on factor 2. Write $\lambda_i$ for the loading of indicator $i$ on its designated factor and $\psi_i$ for its error variance. Set

$$\Phi=\begin{pmatrix}1&\varphi\\\varphi&1\end{pmatrix},\qquad \Psi=\operatorname{diag}(\psi),\qquad \Sigma=\Lambda\Phi\Lambda^{\mathsf T}+\Psi.$$

The covariance formula is defined algebraically for all real inputs. The model uses $|\varphi|\le 1$ and $\psi_i\ge 0$. Lean indexes the five indicators from zero. See [identification of a correlated two-factor model](identification-of-a-correlated-two-factor-model.md) for what can be recovered from $\Sigma$.
