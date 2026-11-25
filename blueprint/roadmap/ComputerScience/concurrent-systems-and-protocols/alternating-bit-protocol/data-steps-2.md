# Data-channel transitions of the alternating-bit protocol with data

The data channel is a
lossy one-place channel whose content is either empty or a pair $(b, d)$ of a sequence bit $b$
and a data bit $d$. Its transitions, as a list of pairs of a label and a successor content: the
empty channel inputs on $\mathsf{send}(b, d)$ and then holds $(b, d)$, for the four pairs $(b, d)$
in the order $(\mathrm{false}, \mathrm{false})$, $(\mathrm{false}, \mathrm{true})$,
$(\mathrm{true}, \mathrm{false})$, $(\mathrm{true}, \mathrm{true})$; a channel holding $(b, d)$
either outputs on $\mathsf{recv}(b, d)$ and becomes empty, or loses the frame by a silent step
$\tau$ and becomes empty.
