# A Common-legal step stores each writer's value

Let $\mathit{mem} : \mathbb{N} \to \alpha$ be a memory and $s$ a PRAM step that is CRCW-Common-legal for $\mathit{mem}$. If processor $i$ has write address $a$, then the Priority CRCW step stores $i$'s value in cell $a$:

$$\mathrm{stepCRCW}(\mathit{mem}, s)(a) = \mathrm{writeVal}(\mathit{mem}, s, i).$$
