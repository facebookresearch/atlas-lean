# Forgery bound for HMAC on finite encoded messages

Let the chaining values $S$ be finite and nonempty with decidable equality, the messages $X$ finite with decidable equality and $\mathrm{enc} : X \to \{0,1\}^*$ an arbitrary encoding. For every forger $A$ with arbitrary coins $A.\mathrm{coins}$, there are coins $r$ in the support of $A.\mathrm{coins}$ such that

$$
\Pr[A \text{ forges against HMAC on } \mathrm{enc}] \le \mathrm{Adv}^{\mathrm{prf}}_F(D_r) + \frac{1}{|S|},
$$

where $F(k, x) = \mathrm{HMAC}_k(\mathrm{enc}(x))$ with $k$ uniform on $\{0,1\}^n$, and $D_r$ is the deterministic distinguisher that runs $A$ with coins $r$, answering its tagging queries with its oracle, then queries the forged message and accepts when the answer is the forged tag and the message was not queried before. The PRF advantage is $\mathrm{Adv}^{\mathrm{prf}}_F(D) = |\Pr[D^{F(k,\cdot)} = 1] - \Pr[D^{f} = 1]|$, with uniform coins for $D$, a uniform key $k$ and a uniformly random function $f : X \to S$. This is the concrete bound in the proof of Katz and Lindell, Theorem 4.6, for HMAC as a keyed function. The term $1/|S|$ is the probability of guessing a tag on a fresh message, so the bound is a concrete forgery estimate, not by itself a security implication: with $|S| = 1$ the real and random tag functions agree, yet guessing the only tag succeeds with probability $1$. An asymptotic MAC-security corollary also needs $1/|S|$ to be negligible and the distinguisher to be admissible.
