# Product of the history multiplicities

For a binary feature matrix $Z$ with $N$ rows, the product $\prod_{h \in \{0, 1\}^N} K_h!$ of the factorials of the [history counts](history-count.md). It is the number of column orders of $Z$ that give the same matrix, and divides $K!$ in the cardinality $K!/\prod_h K_h!$ of a lof-equivalence class. When $Z$ has no zero column, only the histories $h \ne 0$ contribute, as in Equation 14 of the source.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.2.
