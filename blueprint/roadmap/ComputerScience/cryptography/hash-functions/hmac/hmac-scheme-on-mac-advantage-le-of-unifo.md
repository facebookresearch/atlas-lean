# Forgery bound for HMAC against forgers with uniform coins

Let the chaining values $S$ be finite and nonempty with decidable equality, the messages $X$ finite with decidable equality, $\mathrm{enc} : X \to \{0,1\}^*$ an encoding, and the coins $R$ finite and nonempty. For a forger $A$ whose coins are uniform on $R$,

$$
\Pr[A \text{ forges against HMAC on } \mathrm{enc}] \le \mathrm{Adv}^{\mathrm{prf}}_F(D) + \frac{1}{|S|},
$$

where $F(k, x) = \mathrm{HMAC}_k(\mathrm{enc}(x))$ and $D$ is the distinguisher with uniform coins $r \in R$ that, at coins $r$, runs the forger, queries the forged message and accepts on a matching tag for a fresh message. The PRF advantage is $\mathrm{Adv}^{\mathrm{prf}}_F(D) = |\Pr[D^{F(k,\cdot)} = 1] - \Pr[D^{f} = 1]|$, with uniform coins for $D$, a uniform key $k$ and a uniformly random function $f : X \to S$. This is the concrete bound in the proof of Katz and Lindell, Theorem 4.6. The term $1/|S|$ is the probability of guessing a tag on a fresh message, so the bound is a concrete forgery estimate, not by itself a security implication: with $|S| = 1$ the real and random tag functions agree, yet guessing the only tag succeeds with probability $1$. An asymptotic MAC-security corollary also needs $1/|S|$ to be negligible and the distinguisher to be admissible.
