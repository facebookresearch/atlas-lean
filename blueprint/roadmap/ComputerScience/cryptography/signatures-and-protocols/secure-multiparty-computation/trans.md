# One-exchange quantitative transitivity

Suppose $\pi$ emulates $\phi$ with overhead $\delta_1$ and slack $\varepsilon_1$, and $\phi$
emulates $\psi$ with overhead $\delta_2$ and slack $\varepsilon_2$, in the one-exchange model.
Then $\pi$ emulates $\psi$: for every intermediary with upper clock $t_A$, the final simulator
costs at most $\delta_2(\delta_1(t_A(k)))$ at each parameter $k$. For every environment with
budget $t_E$ at $k$ and every auxiliary input, the output-bit total variation distance is
strictly less than $\varepsilon_1(t_E)+\varepsilon_2(t_E)$. This chains comparisons of bit
laws; it is not a theorem about replacing a subroutine inside a protocol.
