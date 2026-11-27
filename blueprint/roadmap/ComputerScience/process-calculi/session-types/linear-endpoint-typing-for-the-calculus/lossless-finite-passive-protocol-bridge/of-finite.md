# Embedding of finite passive-name protocols

The embedding $\iota$ of finite binary session types into protocols is defined by
$\iota(\mathrm{end}) = \mathrm{end}$, $\iota({!S}) = {!\mathrm{N}}.\iota(S)$ and $\iota({?S}) =
{?\mathrm{N}}.\iota(S)$: every send and receive becomes a send or receive of a passive name.
