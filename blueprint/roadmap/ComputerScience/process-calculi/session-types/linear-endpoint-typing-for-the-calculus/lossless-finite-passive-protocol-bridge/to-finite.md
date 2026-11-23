# Partial recovery of a finite passive-name protocol

The partial map $\pi$ from protocols to finite binary session types is defined by $\pi(\mathrm{end})
= \mathrm{end}$, $\pi({!\mathrm{N}}.S) = {!\pi(S)}$ and $\pi({?\mathrm{N}}.S) = {?\pi(S)}$
(undefined whenever $\pi(S)$ is undefined), and $\pi$ is undefined on endpoint sends ${!(r,k,T)}.S$,
endpoint receives ${?(r,k,T)}.S$ and graph cursors.
