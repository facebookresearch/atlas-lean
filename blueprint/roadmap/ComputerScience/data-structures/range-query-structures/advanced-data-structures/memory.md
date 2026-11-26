# Cell-probe memory

Cell-probe memory with `cells` addresses and word width `width` is the total map
`Fin cells → BitVec width`. Each address has exactly one word; addresses need not fit in a
word. With zero cells there are no addresses, and with zero width there is one possible word.
