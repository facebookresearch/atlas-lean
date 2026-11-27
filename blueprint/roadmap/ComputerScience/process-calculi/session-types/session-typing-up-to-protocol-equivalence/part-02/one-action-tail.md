# Output typing at a code equivalent to one send then end

Let $n$, $k$ be natural numbers, $\Gamma$ an ownership context all of whose capabilities have head
$\mathrm{end}$ and all of whose endpoints have names scoped at depth $n$, $d$ an endpoint with name
$x$ scoped at depth $n$, $b$ a name scoped at depth $n$ and $T$ a protocol with
${!\mathrm{N}}.\mathrm{end} \simeq T$. Then $\Gamma[d \mapsto (k,T)] \vdash^{\simeq}_n
\overline{x}\langle b\rangle.\mathbf{0}$.
