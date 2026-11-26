# A CREW-legal step stores the writer's value

Let $s$ be a CREW-legal PRAM step and $\mathit{mem} : \mathbb{N} \to \alpha$ a memory. If processor $i$ has write address $a$, then the Priority CRCW step stores $i$'s value in cell $a$:

$$\mathrm{stepCRCW}(\mathit{mem}, s)(a) = \mathrm{writeVal}(\mathit{mem}, s, i).$$
