# Forgery bound for HMAC on length-bounded bit strings

Let the chaining values $S$ be finite and nonempty with decidable equality, and let $\mathrm{maxLen} \in \mathbb{N}$. For every forger $A$ with arbitrary coins whose tagging queries and forgery are bit strings shorter than $\mathrm{maxLen}$ (a forger on those messages, run against HMAC on all bit strings), there are coins $r$ in the support of $A.\mathrm{coins}$ such that

$$
\Pr[A \text{ forges against HMAC}] \le \mathrm{Adv}^{\mathrm{prf}}_F(D_r) + \frac{1}{|S|},
$$

where $F(k, x) = \mathrm{HMAC}_k(x)$ on the finite set of bit strings shorter than $\mathrm{maxLen}$, with $k$ uniform on $\{0,1\}^n$, and $D_r$ is the deterministic distinguisher built from $A$ at coins $r$ (run the forger, query the forged message, accept on a matching tag for a fresh message). The length bound makes the message space finite, as the random-function experiment requires. The PRF advantage is $\mathrm{Adv}^{\mathrm{prf}}_F(D) = |\Pr[D^{F(k,\cdot)} = 1] - \Pr[D^{f} = 1]|$, with a uniform key $k$ and a uniformly random function $f$ from the bit strings shorter than $\mathrm{maxLen}$ to $S$. This is the concrete bound in the proof of Katz and Lindell, Theorem 4.6. The term $1/|S|$ is the probability of guessing a tag on a fresh message, so the bound is a concrete forgery estimate, not by itself a security implication: with $|S| = 1$ the real and random tag functions agree, yet guessing the only tag succeeds with probability $1$. An asymptotic MAC-security corollary also needs $1/|S|$ to be negligible and the distinguisher to be admissible.
