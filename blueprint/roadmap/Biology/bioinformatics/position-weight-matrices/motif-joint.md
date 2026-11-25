# Joint likelihood of a sequence and a motif occurrence

For a finite latent set $Z$, a background $q$, a prior $\pi$ on $Z$, a map assigning to each $z$ a start $j \le n$ or "no occurrence", a site model $\theta$ and a sequence $x$ of length $n + w$, the joint likelihood is $\pi(z)\, \beta(x)\, r(z)$, where $\beta$ is the [background likelihood](bg-lik.md) and $r(z)$ the [window ratio](window-ratio.md) of the start of $z$.

It is the joint probability of $x$ and $z$ when $q$ is a probability law with $q(b) > 0$, the columns of $\theta$ are probability laws and $\pi$ is a probability law on $Z$: one occurrence per sequence takes $Z = \{0, \dots, n\}$ with uniform $\pi$; zero or one occurrence takes $Z = \{\text{none}, 0, \dots, n\}$ with $\pi(\text{none}) = 1 - \gamma$ and $\pi(j) = \gamma / (n + 1)$ for a fixed $0 \le \gamma \le 1$.
