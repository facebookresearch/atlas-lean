# Joint law on rectangles

Let $P$ be a measure on a measurable space $\Omega$, and let $X : \Omega \to \mathcal{X}$ and $Y : \Omega \to \mathcal{Y}$ be $P$-almost everywhere measurable maps into measurable spaces. For measurable sets $s \subseteq \mathcal{X}$ and $t \subseteq \mathcal{Y}$, the pushforward of $P$ under $\omega \mapsto (X(\omega), Y(\omega))$ gives the rectangle $s \times t$ the measure $P(\{\omega : X(\omega) \in s \text{ and } Y(\omega) \in t\})$. When $P$ is a probability measure, this pushforward is the joint law of $X$ and $Y$, and the value is the probability that both events occur.

## Idea

The joint law of $X$ and $Y$ is the law of the pair $(X, Y)$, seen as one random variable with values in the product space. The preimage of a rectangle $s \times t$ under the pair is the intersection of the preimages of $s$ and $t$, so on rectangles the joint law is simply the probability that $X$ lands in $s$ and $Y$ lands in $t$. For probability measures these values determine the joint law, since rectangles generate the product σ-algebra and are closed under intersection; independence of $X$ and $Y$ says exactly that they factor as $P(X \in s) P(Y \in t)$. For two independent fair dice, the rectangle "first die even" times "second die shows 6" has probability $3/36 = 1/12$.

## Statements

- [Joint law of two random variables on a rectangle](map-prod-mk-apply-prod.md)
