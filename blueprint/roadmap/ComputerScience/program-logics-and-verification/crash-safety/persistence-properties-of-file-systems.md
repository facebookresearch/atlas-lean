# Persistence properties of file systems

A *persistence property* of a file system is a guarantee about which states can be observed after a crash, for example that a rename is atomic (after a crash the name refers to either the old or the new file), that appends are persisted in order, or that an overwrite of a block is atomic. An application's crash consistency is relative to the persistence properties it assumes, which differ between file systems and their configurations.

## Depends on

- [A crash model of disks with volatile caches](the-asynchronous-disk-model-of-crash-hoare-logic.md)

## Sources

- T. S. Pillai, V. Chidambaram, R. Alagappan, S. Al-Kiswany, A. C. Arpaci-Dusseau and R. H. Arpaci-Dusseau, "All file systems are not created equal: on the complexity of crafting crash-consistent applications", *OSDI 2014*
