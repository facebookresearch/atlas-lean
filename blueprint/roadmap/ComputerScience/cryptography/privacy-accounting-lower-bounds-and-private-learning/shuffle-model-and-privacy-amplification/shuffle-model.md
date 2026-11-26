# Local randomizers and the shuffle model

A randomized map $R : \mathcal{X} \to \mathcal{Y}$ is an **$\varepsilon_0$-differentially private local randomizer** if $\Pr[R(x) \in E] \le e^{\varepsilon_0}\Pr[R(x') \in E]$ for all inputs $x, x'$ and events $E$. In the **local model**, each of $n$ users holding $x_i$ sends $R(x_i)$ to an untrusted analyzer. In the **shuffle model**, users send (one or several) locally randomized messages through a trusted shuffler that outputs the multiset of all messages in uniformly random order, so the analyzer sees the messages but not who sent them. A shuffle protocol is **$(\varepsilon,\delta)$-differentially private** if the shuffler's output, as a function of the dataset $(x_1, \dots, x_n)$, is $(\varepsilon,\delta)$-DP. The model sits between the local model and the central (trusted curator) model.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Sources

- A. Cheu, A. Smith, J. Ullman, D. Zeber, M. Zhilyaev, "Distributed Differential Privacy via Shuffling", EUROCRYPT (2019), arXiv:1808.01394.
- U. Erlingsson, V. Feldman, I. Mironov, A. Raghunathan, K. Talwar, A. Thakurta, "Amplification by Shuffling: From Local to Central Differential Privacy via Anonymity", SODA (2019), arXiv:1811.12469.
