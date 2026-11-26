# Decay-rate certificate for the network SIS model

**Setting.** Locations $i=1,\dots,n$ have infected fractions $x_i(t)\in[0,1]$ evolving by the network SIS model

$$\dot x_i=(1-x_i)\sum_{j=1}^n\beta a_{ij}x_j-\gamma x_i,\qquad\text{i.e.}\quad \dot x=\mathrm{diag}(\mathbf{1}-x)\,\beta Ax-\gamma x,$$

with transmission rate $\beta$, recovery rate $\gamma$ and a nonnegative mixing matrix $A=(a_{ij})$. When residents of location $i$ (population $N_i$) spend fraction $\tau_{il}$ of their time at location $l$, infection is acquired in proportion to prevalence among those present, which gives

$$a_{ij}=\sum_{l=1}^n\tau_{il}\tau_{jl}\frac{N_j}{\sum_kN_k\tau_{kl}},\qquad A=C B^\top,\ C=\tau,\ B^\top=D_1\tau^\top D_2,$$

with $D_1=\mathrm{diag}\big(\sum_kN_k\tau_{kl}\big)^{-1}$ and $D_2=\mathrm{diag}(N_1,\dots,N_n)$. For a matrix $P$ with nonnegative off-diagonal entries, $\lambda_{\max}(P)$ denotes its Perron–Frobenius eigenvalue.

**Theorem.** Let $A$ be strongly connected (irreducible) and $\alpha\ge0$.

1. If $\lambda_{\max}(\beta A-\gamma I)\le-\alpha$, then there is a positive linear combination $\sum_iv_ix_i(t)$ (with $v$ the left Perron eigenvector) that decays to zero at rate $\alpha$ from every initial condition and every starting time.
2. Conversely, if $\lambda_{\max}(\beta A-\gamma I)>-\alpha$, there is an initial condition $x(0)>0$ from which no positive linear combination of the $x_i(t)$ decays at rate $\alpha$.

An analogous certificate holds for a two-class (asymptomatic and symptomatic) COVID-19 network model in terms of $\lambda_{\max}(M(t_0))$, where $M(t_0)$ is its linearization weighted by the current susceptible fractions $s(t_0)>0$.

So, although the dynamics is nonlinear, a guaranteed exponential decay rate of the epidemic reduces to a linear eigenvalue bound.

## Expansion

Let $v>0$ be the left Perron eigenvector of $\beta A-\gamma I$, with eigenvalue $\lambda=\lambda_{\max}$. Since $1-x_i\le1$ and the off-diagonal entries are nonnegative, $\frac{d}{dt}v^\top x=\beta v^\top\mathrm{diag}(\mathbf 1-x)Ax-\gamma v^\top x\le v^\top(\beta A-\gamma I)x=\lambda v^\top x$, so $v^\top x(t)\le e^{\lambda(t-t_0)}v^\top x(t_0)$, which gives part 1. For the converse, near $x=0$ the dynamics is close to the linear system $\dot x=(\beta A-\gamma I)x$; starting along the right Perron eigenvector, every positive combination decays no faster than $e^{\lambda t}$ up to lower-order terms, which is slower than $e^{-\alpha t}$.

## Sources

- Qianqian Ma, Yang-Yu Liu, Alex Olshevsky, "Optimal Lockdown for Pandemic Control", arXiv:2010.12923 (2020): Supplementary sections "Network SIS Model", "Construction of The Matrix $A$" and "Stability of The Network SIS and COVID-19 Models" (decay propositions for the SIS and COVID-19 models). <https://doi.org/10.48550/arXiv.2010.12923> Published version: IEEE Transactions on Automatic Control 69 (2024) 4538–4553, <https://doi.org/10.1109/tac.2023.3340556>.
