# Identification forces full response

Full-data laws are measures on $\{0,1\} \times \mathbb R$, a point $(r, y)$ recording the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. The observed data of $(r, y)$ are $o(r, y) = (r, y)$ if $r = 1$ and $o(r, y) = (0, 0)$ if $r = 0$; the observed-data law of $P$ is the pushforward $P \circ o^{-1}$. Let $P$ be a probability measure on $\{0,1\} \times \mathbb R$ with $y$ integrable, and let $F$ be any real-valued function of measures on $\{0,1\} \times \mathbb R$. Suppose $F$ recovers the full-data mean from the observed-data law at every law observationally equivalent to $P$: for every probability measure $Q$ with $y$ integrable and $Q \circ o^{-1} = P \circ o^{-1}$,

$$F(Q \circ o^{-1}) = \int y \, dQ.$$

Then $P(r = 0) = 0$. Equivalently, without a model of the nonresponse mechanism the mean is identified at no law with positive nonresponse probability.
