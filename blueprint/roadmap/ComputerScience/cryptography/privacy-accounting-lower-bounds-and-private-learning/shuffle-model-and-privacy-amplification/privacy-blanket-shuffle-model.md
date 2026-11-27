# Privacy blanket amplification and single-message summation in the shuffle model

Every local randomizer $R$ can be written as a mixture $R(x) = (1 - \gamma) R'(x) + \gamma\,\omega$ with a data-independent **privacy blanket** distribution $\omega$, where $\gamma$, the total variation similarity of $R$, is the mass shared by all output distributions; for an $\varepsilon_0$-local randomizer $\gamma \ge e^{-\varepsilon_0}$. Blanket mass alone does not bound the amplification: a randomizer that reports its input with probability $1/2$ and a uniform symbol of $[k]$ otherwise has $\gamma = 1/2$, yet a changed symbol appears with probability at least $1/2$ on one dataset and at most about $n/(2k)$ on the other, so for $k \gg n$ no small privacy bound holds for small fixed $\delta$; the local privacy parameter enters as well. For an $\varepsilon_0$-local randomizer with $\varepsilon_0 \le \log\bigl(n/\log(1/\delta)\bigr)/2$, the shuffled mechanism is $(\varepsilon, \delta)$-differentially private with

$$
\varepsilon = O\!\left((1 \wedge \varepsilon_0)\, e^{\varepsilon_0} \sqrt{\frac{\log(1/\delta)}{n}}\right),
$$

which extends earlier shuffle amplification to a wider range of $\varepsilon_0$; a more general mechanism-dependent bound in terms of the privacy amplification random variables of $R$ and the blanket count $\mathrm{Bin}(n, \gamma)$ gives sharper numbers for specific randomizers. As an application, consider summation of real inputs $x_i \in [0,1]$ in the single-message shuffle model, with accuracy measured by the worst-case mean squared error over all inputs. For $0 < \varepsilon \le 1$ and $0 < \delta < 1/2$ there is an $(\varepsilon,\delta)$-differentially private protocol with worst-case mean squared error $O\big(n^{1/3}\log^{2/3}(1/\delta)/\varepsilon^{4/3}\big)$ (Theorem 4.1), and every $(\varepsilon,\delta)$-differentially private single-message protocol with such $\delta$ has worst-case mean squared error $\Omega(n^{1/3})$, with a constant depending on $\varepsilon$ (Theorem 4.2). So for fixed $\varepsilon$ and $\delta$ in these ranges the optimal worst-case mean squared error is $\Theta(n^{1/3})$, whereas local protocols have mean squared error $\Theta(n)$.

## Proof sketch

Decompose the output law as a common part plus a data-dependent remainder; conditioned on which users drew from the blanket, the shuffled output depends on the differing user only through its non-blanket report, hidden among a binomial number of blanket samples. Via hockey-stick divergences, the privacy loss is bounded by an expectation over the number $M \sim \mathrm{Bin}(n, \gamma)$ of blanket samples of the positive part of a sum of $M$ i.i.d. bounded privacy amplification random variables, whose range and mean depend on $\varepsilon_0$; a Hoeffding-type bound for this sum and concentration of $M$ give the corollary. The summation protocol randomizes discretized values with a blanket that is uniform over the message space; the lower bound analyzes the counts any single-message protocol must reveal.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Amplification by shuffling from local to central privacy](amplification-by-shuffling-local-to-central.md)

## Sources

- B. Balle, J. Bell, A. Gascon, K. Nissim, "The Privacy Blanket of the Shuffle Model", CRYPTO (2019), arXiv:1903.02837, Lemmas 5.1–5.3, Theorem 5.3, Corollary 5.3.1, Section 4 and Theorems 4.1 and 4.2.
