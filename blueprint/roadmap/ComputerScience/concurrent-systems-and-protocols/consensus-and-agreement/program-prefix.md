# Program Prefix

A finite prefix of program and channel steps, before tick `T`. The indexed crash set is
external: no action can be taken by its actor after it crashes. Program slots strictly advance
locally; unnumbered inbox, fanout and delivery actions need not advance the program counter.
