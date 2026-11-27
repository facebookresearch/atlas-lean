# x86-TSO storage events

The six storage events are a read, a write, a flush, a fence (MFENCE), lock acquisition, and
lock release. Each records the acting thread. Reads and writes also record an address and a
value; the other four carry no additional data. The same read label is used whether the value
comes from memory or a buffer. A flush is the thread-indexed internal propagation event $\tau$.
