# Head and branch matching of protocols up to a child relation

Let $\mathcal{R}$ be a binary relation on protocols. The head match $\mathcal{H}(\mathcal{R})$
relates two protocols exactly in the following cases:

- $\mathrm{end}$ and $\mathrm{end}$;
- ${!\mathrm{N}}.S$ and ${!\mathrm{N}}.T$, and ${?\mathrm{N}}.S$ and ${?\mathrm{N}}.T$, whenever $S
  \mathrel{\mathcal{R}} T$;
- ${!(r,k,P)}.S$ and ${!(r,k,Q)}.T$, and ${?(r,k,P)}.S$ and ${?(r,k,Q)}.T$, with the same polarity
  $r$ and rank $k$, whenever $P \mathrel{\mathcal{R}} Q$ and $S \mathrel{\mathcal{R}} T$.
