# Break-even concentrations and local competitive exclusion in the two-species chemostat

**Model.** A culture vessel is fed at dilution rate $D>0$ with substrate at concentration $S_{in}$. Species $B_1,B_2$ consume substrate $S$ with specific growth rates $\mu_i(S)$ (increasing, $\mu_i(0)=0$) and yields $k_i>0$:

$$
\frac{dS}{dt}=-\frac{\mu_1(S)}{k_1}B_1-\frac{\mu_2(S)}{k_2}B_2+D(S_{in}-S),\qquad \frac{dB_i}{dt}=\bigl(\mu_i(S)-D\bigr)B_i,\quad i=1,2 .
$$

The **break-even concentration** $\lambda_i$ of species $i$ is the solution (when it exists) of $\mu_i(\lambda_i)=D$, the substrate level at which its growth exactly balances washout.

**Proposition (single species).** For one species ($B_2\equiv0$): if $D<\mu_1(S_{in})$ there are two equilibria, washout $E_0=(S_{in},0)$, unstable, and $E_1=(\lambda_1,k_1(S_{in}-\lambda_1))$, locally exponentially stable; if $D\ge\mu_1(S_{in})$, washout is the only nonnegative equilibrium, locally exponentially stable for $D>\mu_1(S_{in})$ and non-hyperbolic at $D=\mu_1(S_{in})$.

**Proposition (two species).** If $S_{in}>\max(\lambda_1,\lambda_2)$, the competition system has exactly three nonnegative equilibria

$$
E_0=(S_{in},0,0),\qquad E_1=\bigl(\lambda_1,\,k_1(S_{in}-\lambda_1),\,0\bigr),\qquad E_2=\bigl(\lambda_2,\,0,\,k_2(S_{in}-\lambda_2)\bigr).
$$

If $\lambda_i<\lambda_j$, then $E_i$ is locally exponentially stable while $E_0$ and $E_j$ are unstable: the species with the lower break-even concentration wins. If $\lambda_1=\lambda_2$, the two single-species equilibria lie on a line of equilibria through a non-hyperbolic point and the winner switches as the parameters cross this point.

## Depends on

- [Chemostat equilibria and washout](../chemostat/chemostat-equilibria-and-washout.md)

## Expansion

At $E_i$ the Jacobian is block triangular: the rate of the absent species $j$ is $\mu_j(\lambda_i)-D$, negative exactly when $\lambda_i<\lambda_j$ (monotone $\mu_j$), and the $(S,B_i)$ block has trace $-D-\mu_i'(\lambda_i)B_i/k_i<0$ and determinant $D\,\mu_i'(\lambda_i)B_i/k_i>0$, so both eigenvalues have negative real part. At $E_0$ the eigenvalues $\mu_i(S_{in})-D>0$ make washout unstable when $S_{in}>\lambda_i$, and at the losing equilibrium $E_j$ the invader eigenvalue $\mu_i(\lambda_j)-D>0$. Linearization (Lyapunov's indirect method) gives the stated local exponential stability; global competitive exclusion (Hsu–Hubbell–Waltman) holds under monotone kinetics through the conservation of $S+B_1/k_1+B_2/k_2$, which tends to $S_{in}$. In simulations, a three-dimensional reactive-transport code (MIN3P) reproduced the chemostat equilibria away from these bifurcations but deviated markedly near washout and near $\lambda_1=\lambda_2$, where the equilibria are non-hyperbolic.

## Sources

- I. Haidar, F. Gérard and A. Rapaport, "Comparison of numerical simulations of reactive transport and chemostat-like models", arXiv:1108.1772 (2011), Section 2 (chemostat and competition models), Section 3 (single and two-species comparisons) and Appendix (stability definitions, linearization theorem and the propositions on single-species and two-species equilibria), <https://doi.org/10.48550/arXiv.1108.1772>.
