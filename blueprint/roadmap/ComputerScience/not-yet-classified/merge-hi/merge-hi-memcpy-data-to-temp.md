# Merge Hi Memcpy Data To Temp?

Forward bulk copy from main data to distinct temporary storage.  The
recursive memcpy implementation itself requires a pinned call-site tag and a
proof of its physical direction.  Its one-cell primitive is hardwired
data-to-temporary and is used only by this tagged bulk executor.
