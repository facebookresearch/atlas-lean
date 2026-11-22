# Legal runs in the star model

A configuration of the star model assigns to each person $p$
a vertex $\mathrm{pos}(p)$ of the star graph $\mathcal{S}(k)$ and to each vertex $v$ a number
$\mathrm{tor}(v)$ of torches. A finite sequence $\sigma = (S_1, \dots, S_\ell)$ of steps, each a
finite list of movements, is a legal run from the configuration $(\mathrm{pos}, \mathrm{tor})$
when each step $S_i$ is legal from the configuration reached after $S_1, \dots, S_{i-1}$ (a step
updates the positions of the persons and the torch counts) and every person is at a leaf in the
configuration reached after all of $\sigma$. In particular, the empty sequence is a legal run
exactly when every person already stands at a leaf.

## Sources

- Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6, Definition (the star model).
