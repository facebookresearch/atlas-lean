# Unwritten cells are unchanged by a PRAM step

If no processor of the PRAM step $s$ has write address $a$, then the Priority CRCW step leaves cell $a$ unchanged: $\mathrm{stepCRCW}(\mathit{mem}, s)(a) = \mathit{mem}(a)$ for every memory $\mathit{mem}$.
