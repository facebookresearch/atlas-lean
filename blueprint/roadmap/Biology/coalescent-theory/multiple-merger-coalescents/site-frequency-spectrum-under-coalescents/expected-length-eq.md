# First-step decomposition of the expected branch lengths

While `b` has at least two
blocks, the expected length of branches subtending `i` copies is the length accumulated in `b`,
`#{blocks of size i} / λ_b`, plus the average over the first merger `K` (probability
`λ_{b,|K|} / λ_b`) of the expected length after it. This follows from the occupation-sum
definition; its block-count counterpart is the first-jump recursion (8) of Birkner, Blath &
Eldon (2013).
