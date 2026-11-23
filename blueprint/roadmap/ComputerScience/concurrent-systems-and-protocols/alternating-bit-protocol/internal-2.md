# Internal channels of the alternating-bit protocol with data

The list of the channel names
that the protocol restricts: $\mathsf{send}(b, d)$ followed by $\mathsf{recv}(b, d)$ for the pairs
$(b, d)$ in the order $(\mathrm{false}, \mathrm{false})$, $(\mathrm{false}, \mathrm{true})$,
$(\mathrm{true}, \mathrm{false})$, $(\mathrm{true}, \mathrm{true})$, then
$\mathsf{reply}(\mathrm{false})$, $\mathsf{reply}(\mathrm{true})$, $\mathsf{ack}(\mathrm{false})$
and $\mathsf{ack}(\mathrm{true})$.
