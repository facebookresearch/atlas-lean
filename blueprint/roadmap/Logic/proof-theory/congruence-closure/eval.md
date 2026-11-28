# Eval

Let $D$ be a set, $f \colon \mathbb{N} \to D$ and $\mathrm{op} \colon D \times D \to D$. The value $[\![t]\!] \in D$ of a ground term $t$ is defined recursively by

$$[\![c_c]\!] = f(c), \qquad [\![\mathrm{app}(t, s)]\!] = \mathrm{op}\bigl([\![t]\!], [\![s]\!]\bigr).$$
