# Existential abstraction of a labelled transition system

Let $L$ be a labelled transition system with states $S$ and labels $\Lambda$, given by its transition relation $s \xrightarrow{\mu} t$, and let $\alpha : S \to T$ be any function. The existential (direct-image) abstraction of $L$ along $\alpha$ is the labelled transition system $L_\alpha$ with states $T$ and the same labels $\Lambda$, in which

$$a \xrightarrow{\mu} b \text{ in } L_\alpha \iff \exists\, s, t \in S,\ \alpha(s) = a,\ \alpha(t) = b,\ s \xrightarrow{\mu} t \text{ in } L.$$

No surjectivity is required of $\alpha$; an abstract state outside the image of $\alpha$ has no transitions in or out.
