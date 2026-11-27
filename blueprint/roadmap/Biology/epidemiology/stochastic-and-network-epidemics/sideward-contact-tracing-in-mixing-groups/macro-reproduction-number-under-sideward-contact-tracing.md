# Macro reproduction number and outbreak threshold under sideward contact tracing

**Model (SIR epidemic with mixing groups).** In a population of size $n$, mixing events occur at rate $n\beta$; each gathers $C^{(n)}$ individuals chosen uniformly at random, with $C^{(n)} \to C$ in distribution, $P(C = c) = p_C(c)$ for $c \ge 2$, and finite mean $\mu_C$. In an event of size $c$ each infective infects each susceptible present independently with probability $\pi_c$. Infectives recover at rate $\gamma$ and are diagnosed (and isolated) at rate $\delta$. **Sideward tracing:** when an individual is diagnosed, the event at which they were infected is detected, and each other individual infected at that same event is traced independently with probability $p \in [0,1]$ and removed if still infectious (the infector and the index case's own infectees are not traced).

**Early-phase approximation.** As $n \to \infty$ with a fixed number $m$ of initial infectives, an infective joins mixing events at rate $\beta\mu_C$, the size of such an event is size-biased, $P(\tilde C = c) = c\,p_C(c)/\mu_C$, and the number infected at it is $\tilde Z \sim \mathrm{MixBin}(\tilde C - 1, \pi_{\tilde C})$. Without tracing the basic reproduction number is $R_0 = \frac{\beta}{\gamma+\delta}\,E[C(C-1)\pi_C]$. With tracing, individuals infected at the same event (a *sibling group*) have dependent lifetimes, so the infective process is a branching process with sibling dependence.

**Sibling-group (macro) process.** The number $Y(t)$ of still-infectious members of a sibling group, $Y(0) \sim \tilde Z$, is a Markov jump process absorbed at $0$ with rates, for $i \ge 1$,

$$q_{i,i-1} = i\gamma + i\delta(1-p)^{i-1}, \qquad q_{i,j} = i\delta\binom{i-1}{i-j-1}(1-p)^{j}p^{\,i-j-1}\quad (0 \le j \le i-2).$$

Its jump chain has transition probabilities $p_{i,j} = q_{i,j}/(i(\gamma+\delta))$. Let $m_{00} = 0$ and define recursively

$$m_{i0} = 1 + \sum_{j=1}^{i-1} p_{i,j}\, m_{j0}\qquad (i \ge 1),$$

the expected number of jumps to absorption from $i$. Sibling groups are independent and form a Crump–Mode–Jagers process $\mathcal M$ in which a group of current size $Y(t)$ produces new groups at rate $\beta\mu_C Y(t)$.

**Theorem (macro reproduction number).** The mean number of sibling groups produced by one sibling group is

$$R_e = \frac{\beta}{\gamma+\delta}\sum_{c=2}^{\infty} c\,p_C(c)\sum_{i=1}^{c-1} m_{i0}\binom{c-1}{i}\pi_c^{\,i}(1-\pi_c)^{c-i-1}.$$

**Proposition (individual and macro numbers agree).** If $G_{CT}$ is the number of mixing events a typical infective (in the traced process) attends while infectious, the individual reproduction number $R_e^{(ind)} = E[G_{CT}]\,E[\tilde Z]$ equals $R_e$. When $p = 0$, $m_{i0} = i$ and $R_e = R_0$.

**Theorem (threshold and extinction).** Let $f_X(s) = \frac{\gamma+\delta}{\gamma+\delta+\beta\mu_C(1-s)}$ and let $N$ be the absorption time of the jump chain started from $Y(0) \sim \tilde Z$. Let $z_{\mathcal M}$ be the smallest root in $[0,1]$ of $s = E[f_X(s)^N]$. Then the early-epidemic process with $m \ge 1$ initial infectives dies out almost surely if $R_e \le 1$; if $R_e > 1$ it grows without bound with probability $1 - z^m$, where

$$z = \frac{\gamma+\delta}{\gamma+\delta+\beta\mu_C(1 - z_{\mathcal M})} < 1 .$$

Thus a major outbreak has positive probability in the large-population limit if and only if $R_e > 1$.

## Proof sketch

Between consecutive jumps of the sibling group's size, a group of current size $i$ lives an $\mathrm{Exp}(i(\gamma+\delta))$ time and produces new groups at rate $i\beta\mu_C$. So the number $X_k$ of groups produced between jumps is geometric with mean $\beta\mu_C/(\gamma+\delta)$, independent of $i$. Wald's identity then gives $R_e = E[X]\,E[N]$, and conditioning on $Y(0)$ together with first-step analysis gives the recursion for $m_{i0}$. For the proposition, a member of a group of initial size $i$ has size-biased law $P(\tilde Y_0 = i) = iP(Y_0 = i)/E[Y_0]$, and $i\,E[G_{CT}\mid \tilde Y_0 = i] = E[H \mid Y_0 = i]$. Summing gives $E[G_{CT}] = E[H]/E[\tilde Z]$. For the threshold, the ancestor cannot be traced, so it starts a geometric number $J$ of groups with parameter $(\gamma+\delta)/(\gamma+\delta+\beta\mu_C)$. Hence $z = E[z_{\mathcal M}^J]$, and $z < 1$ if and only if $z_{\mathcal M} < 1$, which by standard branching theory happens if and only if $R_e > 1$. Tracing has no effect when all events have size 2. Its effect grows with the variance of the event size, so heavy-tailed gathering sizes make sideward tracing most effective.

## Sources

- Dongni Zhang and Martina Favero, "Sideward Contact Tracing in an Epidemic Model with Mixing Groups", *Methodology and Computing in Applied Probability* 27 (2025), 33, <https://doi.org/10.1007/s11009-025-10160-y>. Preprint version: arXiv:2407.11622 (2024), Section 2 (model), Section 3 (early epidemic approximation), Section 4 (macro branching process), Section 5 (Theorem 5.1, Proposition 5.2, Theorem 5.4), <https://doi.org/10.48550/arXiv.2407.11622>.
