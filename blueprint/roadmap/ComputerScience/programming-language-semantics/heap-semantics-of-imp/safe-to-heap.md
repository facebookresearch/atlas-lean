# Embedded plain commands are safe

For every plain IMP command $c$ with embedding
$\overline{c}$ into the heap language, every store $s$ and every heap $h$, the heap
configuration $(\overline{c}, s, h)$ is safe.

This holds because plain IMP never gets stuck except at $\mathtt{skip}$.
