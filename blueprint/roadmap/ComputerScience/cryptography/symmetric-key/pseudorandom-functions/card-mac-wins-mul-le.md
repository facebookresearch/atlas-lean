# Counting forgeries against a random function

Let $M$ and $T$ be finite sets and let $c$ be
an adaptive oracle algorithm that queries messages in $M$, receives tags in $T$ and outputs a pair
in $M \times T$. Call a function $f \colon M \to T$ a win for $c$ when the run of $c$ with oracle
$f$ outputs a pair $(m, t)$ with $f(m) = t$ and $m$ not among the messages queried in that run.
If $W$ is the set of functions $M \to T$ that are wins for $c$, then $|W| \cdot |T| \le |T|^{|M|}$.

Changing the tag of the fresh forged message, which the run never queries, gives $|T|$ functions
with the same run, of which exactly one is a win.
