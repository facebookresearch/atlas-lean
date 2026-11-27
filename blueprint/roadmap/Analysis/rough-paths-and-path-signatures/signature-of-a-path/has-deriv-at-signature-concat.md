# The signature solves $dS = S \otimes dX$

Let every component of the velocity of $X$ be continuous. Then for every real $s$, word $w$ and
letter $i$, the map $t \mapsto S(X)^{w i}_{s,t}$ is differentiable with

$$\frac{d}{dt} S(X)^{w i}_{s,t} = S(X)^{w}_{s,t}\, v^i(t).$$

In tensor notation, $t \mapsto S(X)_{s,t}$ solves the linear controlled differential equation
$dS_{s,t} = S_{s,t} \otimes dX_t$ with $S_{s,s} = 1$. Lyons calls the signature the universal
non-commutative exponential: every linear controlled equation driven by $X$ is solved through it
(see [linear controlled equations are solved by the signature series](tendsto-signature-series.md)).

## Sources

- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, Lemma 4.6.
