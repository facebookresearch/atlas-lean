# Effect of one pointer-jumping round

For every pointer memory $\mathit{ptr} : \mathbb{N} \to \mathbb{N}$, every $n$ and every address $a$, applying the Priority CRCW step to memory $\mathit{ptr}$ with the pointer-jumping step for $\mathit{ptr}$ and $n$ gives

$$\mathrm{stepCRCW}(\mathit{ptr}, \mathrm{pointerJumpStep}(\mathit{ptr}, n))(a) = \begin{cases} \mathit{ptr}(\mathit{ptr}(a)) & a < n, \\ \mathit{ptr}(a) & a \ge n. \end{cases}$$

The new memory is $\mathit{ptr} \circ \mathit{ptr}$ on cells below $n$ and unchanged from $n$ on, where no processor writes. Since the step is CREW-legal, this is also the CREW reading of the round.
