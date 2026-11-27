# One step of a queue operation

For a queue $q$, an enqueue operation with value $v$
performs the costed enqueue of $v$ onto $q$. A dequeue operation performs the costed dequeue
of $q$ and keeps the remaining queue and the cost, discarding the removed value; on an empty
queue the remaining queue is $q$ itself.
