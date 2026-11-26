# Mod-minimizer sampling

The mod-minimizer is a $k$-mer sampling scheme that locates an anchor $t$-mer in each window and samples the $k$-mer whose start is the anchor position reduced modulo the window size $w$. With a random-minimizer anchor its density has a closed form that tends to the optimal $1/w$ as $k \to \infty$; replacing the anchor by a low-density scheme for short $t$-mers (such as the open-closed minimizer) extends that scheme to large $k$.

- [Density of the extended mod-minimizer](density-of-the-extended-mod-minimizer.md)
