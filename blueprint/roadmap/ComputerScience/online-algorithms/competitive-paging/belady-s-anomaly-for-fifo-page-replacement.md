# Belady's anomaly for FIFO page replacement

For the reference string $1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5$, FIFO page replacement starting from an empty memory incurs $9$ page faults with $3$ frames and $10$ page faults with $4$ frames. Hence FIFO can incur more faults with more memory.

## Sources

- Original example: L. A. Belady, R. A. Nelson and G. S. Shedler, "An anomaly in space-time characteristics of certain programs running in a paging machine", *Communications of the ACM* 12(6):349–353, 1969. The reference string and fault counts follow Arpaci-Dusseau and Arpaci-Dusseau, which credits the example to them.
- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, chapter "Beyond Physical Memory: Policies", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-beyondphys-policy.pdf>
