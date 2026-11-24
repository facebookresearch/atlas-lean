# Found New Run Loop Traced singleton write

With one pending run, the collapse helper performs only its final power
write.  This is the loop half of the closed read-then-write regression.
