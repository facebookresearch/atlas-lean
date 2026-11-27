# Signature forgery experiment

The experiment $\mathrm{Sig}\text{-}\mathrm{forge}$ (Katz and Lindell, Definition 12.2) draws
$(pk, sk) \leftarrow \mathrm{Gen}$ and runs the forger on $pk$ with the oracle $\mathrm{Sign}_{sk}$.
The forger outputs a pair $(m, \sigma)$, and the experiment outputs $1$ when
$\mathrm{Vrfy}_{pk}(m, \sigma) = 1$ and $m$ was never queried.
