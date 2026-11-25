# Chain rule, second-coordinate orientation, in nats

Let $\alpha$ and $\beta$ be finite sets and let $p$ be a probability mass function on $\alpha \times \beta$, the joint law of $(X, Y)$. With $H(X, Y)$, $H(Y)$ and $H(X \mid Y)$ the joint entropy, the entropy of the second marginal and the conditional entropy of $X$ given $Y$, all in bits (terms of probability zero contribute $0$), multiplying the chain rule by $\log 2$ gives

$$H(X, Y) \log 2 = H(Y) \log 2 + H(X \mid Y) \log 2,$$

that is, the chain rule $H(X, Y) = H(Y) + H(X \mid Y)$ with all entropies in nats.
