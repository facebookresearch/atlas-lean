# Executions of embedded commands are plain executions

Let $c$ be a plain IMP command,
$s$ a store and $h$ a heap, and write $\overline{d}$ for the embedding of a plain command $d$
into the heap language. If $(\overline{c}, s, h)$ reaches a heap configuration $(c_2, s_2, h_2)$
in zero or more heap steps, then $h_2 = h$ and there is a plain command $c_2'$ with
$c_2 = \overline{c_2'}$ such that $(c, s)$ reaches $(c_2', s_2)$ in zero or more plain small
steps.
