# Balanced layouts exist for every positive worker count

For every public vector of relation lengths and every positive number $p$ of workers there is a balanced bijection of worker slots with input positions. If the total length is $M$, give $M\bmod p$ workers one extra slot beyond $\lfloor M/p\rfloor$ and give the others exactly $\lfloor M/p\rfloor$. There are then exactly $M$ slots to wire, without inspecting any payload. This includes empty inputs and $M<p$.
