# Plain executions lift to the heap language

Let $c, c_2$ be plain IMP commands, $s, s_2$
stores and $h$ a heap, and write $\overline{d}$ for the embedding of a plain command $d$ into the
heap language. If $(c, s)$ reaches $(c_2, s_2)$ in zero or more plain small steps, then
$(\overline{c}, s, h)$ reaches $(\overline{c_2}, s_2, h)$ in zero or more heap steps.
