# MAC forgery experiment

The experiment $\mathrm{Mac}\text{-}\mathrm{forge}$ (Katz and Lindell, Definition 4.2) draws a key
$k \leftarrow \mathrm{Gen}$ and runs the forger with the oracle $\mathrm{Mac}_k$. The forger outputs
a pair $(m, t)$, and the experiment outputs $1$ when $\mathrm{Vrfy}_k(m, t) = 1$ and $m$ was never
queried.
