# The online list-labeling problem

In the *online list-labeling problem* with parameters $n \le m$, a dynamically changing set of at most $n$ elements from a totally ordered universe must be stored in an array of $m$ slots so that the elements appear in sorted order (with gaps). Elements are inserted and deleted online; after each operation the algorithm may move stored elements to other slots, and its *relabeling cost* is the number of elements moved (including the placement of a new element). For randomized algorithms the operation sequence is fixed in advance by an oblivious adversary, independently of the algorithm's random choices. The *linear regime* is $m = (1 + \Theta(1))\, n$, and more generally $m = (1 + \varepsilon) n$.

## Sources

- Alon Itai, Alan G. Konheim, Michael Rodeh, "A Sparse Table Implementation of Priority Queues", ICALP (1981).
- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
