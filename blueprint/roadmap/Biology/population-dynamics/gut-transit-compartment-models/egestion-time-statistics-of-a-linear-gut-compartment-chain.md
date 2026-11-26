# Egestion time statistics of a linear gut compartment chain

**Model.** A gut is a chain of compartments $i = 0, 1, \dots, n$ (e.g. foregut, midgut, hindgut). In compartment $i$ an ingested bacterium has per capita net reproduction rate $r_i = b_i - d_i$ (birth minus death or retention) and moves on to compartment $i + 1$ at rate $m_i > 0$, with exit from compartment $n$ meaning egestion in faeces. With $X_i(t)$ the population in compartment $i$ after a pulse ingestion $X_0(0) = X_0$,

$$\dot X_0 = (r_0 - m_0) X_0, \qquad \dot X_i = m_{i-1} X_{i-1} + (r_i - m_i) X_i \quad (1 \le i \le n),$$

and the egestion flux is $m_n X_n(t)$. Assume $m_i > r_i$ for all $i$ (the population drains out).

**Egestion time distribution.** The egestion flux normalized to unit mass is the density of

$$T = \sum_{i=0}^{n} E_i, \qquad E_i \sim \mathrm{Exp}(m_i - r_i) \ \text{independent},$$

a hypoexponential law, and the total egested output relative to the ingested pulse (a fraction when net growth is negative) is $\prod_{i=0}^{n} m_i/(m_i - r_i)$. Hence the mean and variance of the egestion time are

$$\mu = \sum_{i=0}^{n} \frac{1}{m_i - r_i}, \qquad \sigma^2 = \sum_{i=0}^{n} \frac{1}{(m_i - r_i)^2}.$$

For inert tracers (microspheres, $r_i = 0$) these reduce to $\sum 1/m_i$ and $\sum 1/m_i^2$.

**Consequences.**

- Increasing any net reproduction rate $r_i$ (more growth, less death or retention) increases both $\mu$ and $\sigma^2$; decreasing it shortens and narrows the egestion time distribution, together with a smaller egested fraction. Slower emigration (smaller $m_i$) also increases both.
- If all $K = n + 1$ compartments are identical, $\mu^2/\sigma^2 = K$, so the ratio estimates the effective number of compartments.
- Comparing bacteria with tracers of similar size isolates the demographic terms $r_i$ from transit, and these monotonicity conclusions extend to a broad class of non-compartmental models in which net reproduction declines with residence time.

## Expansion

Each compartment is a linear filter with impulse response $m_i e^{-(m_i - r_i)t}$, so the egestion flux is the convolution of these responses, whose Laplace transform is $\prod_i m_i / (s + m_i - r_i)$. Evaluating at $s = 0$ gives the egested fraction, and dividing by it gives the Laplace transform $\prod_i (m_i - r_i)/(s + m_i - r_i)$ of a sum of independent exponentials, whose cumulants add. The intuition is selection on transit time: when bacteria die or are retained in the gut, the ones that reach the faeces are disproportionately those that passed quickly, which lowers both the mean and the spread of egestion times; growth has the opposite effect. Fitting $\mu$, $\sigma^2$ and the egested fraction from fecal time series of ingested bacteria and microspheres thus distinguishes growth, uniform death and region-specific retention.

## Sources

- H. Inamine, S. P. Ellner, P. D. Newell, Y. Luo, N. Buchon, A. E. Douglas, "Spatiotemporally heterogeneous population dynamics of gut bacteria inferred from fecal time series data", mBio 9 (2018) e01453-17, Results (compartment model, Fig. 4) and Text S2, <https://doi.org/10.1128/mBio.01453-17> (PMC5760738).
