# Embedding preserves termination

Let $c$ be a plain IMP command with embedding
$\overline{c}$ into the heap language, let $s, s'$ be stores and let $h$ be a heap. Then $c$
terminates from $s$ with final store $s'$ if and only if $(\overline{c}, s, h)$ reaches
$(\mathtt{skip}, s', h)$ in zero or more heap steps.
