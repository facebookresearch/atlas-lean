# Conditional entropy lower bound from fiberwise mass bounds under conditioning

Let $\mu$ be a distribution on a finite set $\Omega$ with maps $\mathrm{obs} : \Omega \to O$ and $\mathrm{tgt} : \Omega \to Z$, and let $M > 0$. Suppose $\Pr_\mu[\mathrm{obs} = o, \mathrm{tgt} = z] \le \Pr_\mu[\mathrm{obs} = o]/M$ for all $o, z$. Then for every event $W \subseteq \Omega$ with $\mu(W) > 0$, the conditional law $\mu(\cdot \mid W)$ satisfies

$$
H\big(\mathrm{tgt} \,\big|\, \mathrm{obs}\big)_{\mu(\cdot\mid W)} \ge \log_2 \mu(W) + \log_2 M,
$$

in bits; for $W = \Omega$ this reads $H(\mathrm{tgt}\mid\mathrm{obs}) \ge \log_2 M$.

## Proof sketch

Under $\mu(\cdot\mid W)$ each conditional mass $\Pr[\mathrm{tgt} = z \mid \mathrm{obs} = o, W]$ is at most $\Pr_\mu[\mathrm{obs}=o]/(M\,\Pr_\mu[\mathrm{obs}=o, W])$, so its surprisal is at least $\log_2 M + \log_2(\Pr_\mu[\mathrm{obs}=o,W]/\Pr_\mu[\mathrm{obs}=o])$. Averaging over $o$ under $\mu(\cdot\mid W)$ and applying Jensen's inequality to the logarithm bounds the average of the second term below by $\log_2\mu(W)$.

## Depends on

- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023.
